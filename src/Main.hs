{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Control.Monad.Except
import Data.Functor ((<&>))
import Data.IORef
import Data.Maybe (isJust)
import Numeric
import System.Environment
import System.IO
import Text.ParserCombinators.Parsec hiding (spaces)

type Env = IORef [(String, IORef LispVal)]

type IOThrowsError = ExceptT LispError IO

liftThrows :: ThrowsError a -> IOThrowsError a
liftThrows (Left err) = throwError err
liftThrows (Right val) = pure val

runIOThrows :: IOThrowsError String -> IO String
runIOThrows action = runExceptT (trapError action) <&> extractValue

data Unpacker = forall a. (Eq a) => AnyUnpacker (LispVal -> ThrowsError a)

data LispVal
    = Atom String
    | List [LispVal]
    | DottedList [LispVal] LispVal
    | Number Integer
    | String String
    | Character Char
    | Bool Bool
    | PrimitiveFunc ([LispVal] -> ThrowsError LispVal)
    | Func {params :: [String], vararg :: Maybe String, body :: [LispVal], closure :: Env}
    | IOFunc ([LispVal] -> IOThrowsError LispVal)
    | Port Handle

instance Show LispVal where show = showVal

showVal :: LispVal -> String
showVal (String contents) = "\"" ++ contents ++ "\""
showVal (Atom name) = name
showVal (Number n) = show n
showVal (Bool True) = "#t"
showVal (Bool False) = "#f"
showVal (List contents) = "(" ++ unwordsList contents ++ ")"
showVal (DottedList h t) = "(" ++ unwordsList h ++ " . " ++ showVal t ++ ")"
showVal (Character c) = show c
showVal (PrimitiveFunc _) = "<primitive>"
showVal (Func args varargs _ _) =
    "(lambda ("
        ++ unwords (map show args)
        ++ ( case varargs of
                Nothing -> ""
                Just v -> " . " ++ v
           )
        ++ ") ...)"
showVal (Port _) = "<IO port>"
showVal (IOFunc _) = "<IO primitive>"
data LispError
    = NumArgs Integer [LispVal]
    | TypeMismatch String LispVal
    | Parser ParseError
    | BadSpecialForm String LispVal
    | NotFunction String String
    | UnboundVar String String
    | Default String

instance Show LispError where show = showError

type ThrowsError = Either LispError

showError :: LispError -> String
showError (UnboundVar message varname) = message ++ ": " ++ varname
showError (BadSpecialForm message form) = message ++ ": " ++ show form
showError (NotFunction message func) = message ++ ": " ++ show func
showError (NumArgs expected found) = "Expected " ++ show expected ++ " args; found values " ++ unwordsList found
showError (TypeMismatch expected found) = "Invalid type: expected " ++ expected ++ ",  found " ++ show found
showError (Parser parseErr) = "Parse error at " ++ show parseErr

trapError action = catchError action (return . show)
extractValue :: ThrowsError a -> a
extractValue (Right val) = val

unwordsList :: [LispVal] -> String
unwordsList = unwords . map showVal

escapedChars :: Parser Char
escapedChars = do
    char '\\'
    x <- oneOf "\\\"nrt"
    pure $ case x of
        '\\' -> x
        '"' -> x
        'n' -> '\n'
        'r' -> '\r'
        't' -> '\t'

parseCharacter :: Parser LispVal
parseCharacter = do
    char '\''
    x <- noneOf "\\"
    char '\''
    pure $ Character x

parseString :: Parser LispVal
parseString = do
    char '"'
    x <- many $ escapedChars <|> noneOf "\"\\"
    char '"'
    pure $ String x

parseAtom :: Parser LispVal
parseAtom = do
    first <- letter <|> symbol
    rest <- many (letter <|> digit <|> symbol)
    let atom = first : rest
    pure $ case atom of
        "#t" -> Bool True
        "#f" -> Bool False
        _ -> Atom atom

bases :: Parser Char
bases = char 'e' <|> char 'L'

parseList :: Parser LispVal
parseList = List <$> sepBy parseExpr spaces

parseDottedList :: Parser LispVal
parseDottedList = do
    h <- endBy parseExpr spaces
    t <- char '.' >> spaces >> parseExpr
    pure $ DottedList h t

parseQuoted :: Parser LispVal
parseQuoted = do
    char '\''
    x <- parseExpr
    pure $ List [Atom "quote", x]

parseNumber :: Parser LispVal
parseNumber = parseDecimal1 <|> parseDecimal2 <|> parseHex <|> parseOct <|> parseBin

parseDecimal1 :: Parser LispVal
parseDecimal1 = many1 digit >>= (pure . Number . read)

parseDecimal2 :: Parser LispVal
parseDecimal2 = (string "#d" >> many1 digit) <&> Number . read

parseHex :: Parser LispVal
parseHex = (string "#h" >> many1 hexDigit) <&> Number . hex2dig
  where
    hex2dig = fst . head . readHex

parseOct :: Parser LispVal
parseOct = (string "#o" >> many1 octDigit) <&> Number . oct2dig
  where
    oct2dig = fst . head . readOct

parseBin :: Parser LispVal
parseBin = (string "#b" >> many1 (oneOf "10")) <&> Number . bin2dig
  where
    bin2dig = bin2dig' 0
    bin2dig' digint "" = digint
    bin2dig' digint (x : xs) =
        let old = 2 * digint + (if x == '0' then 0 else 1)
         in bin2dig' old xs

parseBool :: Parser LispVal
parseBool = do
    char '#'
    (char 't' >> pure (Bool True)) <|> (char 'f' >> pure (Bool False))

parseExpr :: Parser LispVal
parseExpr =
    parseAtom
        <|> parseString
        <|> parseBool
        <|> parseNumber
        <|> parseQuoted
        <|> do
            char '('
            x <- try parseList <|> parseDottedList
            char ')'
            pure x

symbol :: Parser Char
symbol = oneOf "!$%&|*+-/:<=>?@^_~"

spaces :: Parser ()
spaces = skipMany1 space

readOrThrow :: Parser a -> String -> ThrowsError a
readOrThrow parser input =
    case parse parser "lisp" input of
        Left err -> throwError $ Parser err
        Right val -> pure val

readExpr = readOrThrow parseExpr

readExprList = readOrThrow (endBy parseExpr spaces)

eval :: Env -> LispVal -> IOThrowsError LispVal
eval _ val@(String _) = return val
eval _ val@(Number _) = return val
eval _ val@(Bool _) = return val
eval _ val@(Character _) = return val
eval env (Atom a) = getVar env a
eval _ (List [Atom "quote", val]) = return val
eval env (List [Atom "if", predicate, conseq, alt]) = do
    result <- eval env predicate
    case result of
        Bool False -> eval env alt
        _ -> eval env conseq
eval env (List [Atom "set!", Atom var, form]) =
    eval env form >>= setVar env var
eval env (List [Atom "define", Atom var, form]) =
    eval env form >>= defineVar env var
eval env (List (Atom "define" : List (Atom var : param) : bo)) =
    makeNormalFunc env param bo >>= defineVar env var
eval env (List (Atom "define" : DottedList (Atom var : param) varargs : bo)) =
    makeVarArgs varargs env param bo >>= defineVar env var
eval env (List (Atom "lambda" : List param : bo)) =
    makeNormalFunc env param bo
eval env (List (Atom "lambda" : DottedList param varargs : bo)) =
    makeVarArgs varargs env param bo
eval env (List (Atom "lambda" : varargs@(Atom _) : bo)) =
    makeVarArgs varargs env [] bo
eval env (List [Atom "load", String filename]) = load filename >>= liftM last . mapM (eval env)
eval env (List (function : args)) = do
    func <- eval env function
    argVals <- mapM (eval env) args
    apply func argVals
eval _ badForm = throwError $ BadSpecialForm "Unrecognized special form" badForm

apply :: LispVal -> [LispVal] -> IOThrowsError LispVal
apply (PrimitiveFunc func) args = liftThrows $ func args
apply (Func{..}) args =
    if num params /= num args && vararg == Nothing
        then throwError $ NumArgs (num params) args
        else (liftIO $ bindVars closure $ zip params args) >>= bindVarArgs vararg >>= evalBody
  where
    remainingArgs = drop (length params) args
    num = toInteger . length
    evalBody e = liftM last $ mapM (eval e) body
    bindVarArgs arg e =
        case arg of
            Just name -> liftIO $ bindVars e [(name, List $ remainingArgs)]
            Nothing -> pure e
apply (IOFunc func) args = func args

isBound :: Env -> String -> IO Bool
isBound envRef var = readIORef envRef <&> isJust . lookup var

getVar :: Env -> String -> IOThrowsError LispVal
getVar envRef var = do
    env <- liftIO $ readIORef envRef
    maybe
        (throwError $ UnboundVar "Getting an unbound variable" var)
        (liftIO . readIORef)
        (lookup var env)

setVar :: Env -> String -> LispVal -> IOThrowsError LispVal
setVar envRef var value = do
    env <- liftIO $ readIORef envRef
    maybe
        (throwError $ UnboundVar "Setting an unbound variable" var)
        (liftIO . flip writeIORef value)
        (lookup var env)
    pure value

defineVar :: Env -> String -> LispVal -> IOThrowsError LispVal
defineVar envRef var value = do
    alreadyDefined <- liftIO $ isBound envRef var
    if alreadyDefined
        then setVar envRef var value >> pure value
        else liftIO $ do
            valueRef <- newIORef value
            env <- readIORef envRef
            writeIORef envRef ((var, valueRef) : env)
            pure value

bindVars :: Env -> [(String, LispVal)] -> IO Env
bindVars envRef bindings = readIORef envRef >>= extendEnv bindings >>= newIORef
  where
    extendEnv b env = (++ env) <$> mapM addBinding b
    addBinding (var, value) = do
        ref <- newIORef value
        pure (var, ref)

car :: [LispVal] -> ThrowsError LispVal
car [List (x : xs)] = pure x
car [DottedList (x : xs) _] = pure x
car [badArg] = throwError $ TypeMismatch "pair" badArg
car badArgList = throwError $ NumArgs 1 badArgList

cdr :: [LispVal] -> ThrowsError LispVal
cdr [List (x : xs)] = pure $ List xs
cdr [DottedList (_ : xs) x] = pure $ DottedList xs x
cdr [badArg] = throwError $ TypeMismatch "pair" badArg
cdr badArgList = throwError $ NumArgs 1 badArgList

cons :: [LispVal] -> ThrowsError LispVal
cons [x, List []] = pure $ List ([x])
cons [x, List xs] = pure $ List (x : xs)
cons [x, DottedList xs l] = pure $ DottedList (x : xs) l
cons [x1, x2] = pure $ DottedList [x1] x2
cons badArgList = throwError $ NumArgs 2 badArgList

eqv :: [LispVal] -> ThrowsError LispVal
eqv [Bool arg1, Bool arg2] = pure $ Bool (arg1 == arg2)
eqv [Number arg1, Number arg2] = pure $ Bool (arg1 == arg2)
eqv [String arg1, String arg2] = pure $ Bool (arg1 == arg2)
eqv [Atom arg1, Atom arg2] = pure $ Bool (arg1 == arg2)
eqv [DottedList xs x, DottedList ys y] = eqv [List $ xs ++ [x], List $ ys ++ [y]]
eqv [List arg1, List arg2] = return $ Bool $ (length arg1 == length arg2) && all eqvPair (zip arg1 arg2)
  where
    eqvPair (x1, x2) =
        case eqv [x1, x2] of
            Left err -> False
            Right (Bool val) -> val
eqv [_, _] = pure $ Bool False
eqv badArgList = throwError $ NumArgs 2 badArgList

primitives :: [(String, [LispVal] -> ThrowsError LispVal)]
primitives =
    [ ("+", numericBinop (+))
    , ("-", numericBinop (-))
    , ("*", numericBinop (-))
    , ("/", numericBinop div)
    , ("quotient", numericBinop quot)
    , ("mod", numericBinop mod)
    , ("remainder", numericBinop rem)
    , ("=", numBoolBinop (==))
    , ("<", numBoolBinop (<))
    , (">", numBoolBinop (>))
    , ("/=", numBoolBinop (/=))
    , (">=", numBoolBinop (>=))
    , ("<=", numBoolBinop (<=))
    , ("&&", boolBoolBinop (&&))
    , ("||", boolBoolBinop (||))
    , ("string=?", strBoolBinop (==))
    , ("string<?", strBoolBinop (>))
    , ("string>?", strBoolBinop (<))
    , ("string<=?", strBoolBinop (<=))
    , ("string>=?", strBoolBinop (>=))
    , ("string?", unaryOp stringp)
    , ("number?", unaryOp numberp)
    , ("symbol?", unaryOp symbolp)
    , ("car", car)
    , ("cdr", cdr)
    , ("cons", cons)
    , ("eq?", eqv)
    , ("eqv?", eqv)
    , ("equal?", equal)
    ]

ioPrimitives :: [(String, [LispVal] -> IOThrowsError LispVal)]
ioPrimitives =
    [ ("apply", applyProc)
    , ("open-input-file", makePort ReadMode)
    , ("open-output-file", makePort WriteMode)
    , ("close-input-port", closePort)
    , ("close-output-port", closePort)
    , ("read", readProc)
    , ("write", writeProc)
    , ("read-contents", readContents)
    , ("read-all", readAll)
    ]

applyProc :: [LispVal] -> IOThrowsError LispVal
applyProc [func, List args] = apply func args
applyProc (func : args) = apply func args

makePort :: IOMode -> [LispVal] -> IOThrowsError LispVal
makePort mode [String filename] = liftM Port $ liftIO $ openFile filename mode

closePort :: [LispVal] -> IOThrowsError LispVal
closePort [Port port] = liftIO $ hClose port >> pure (Bool True)
closePort _ = pure $ Bool False

readProc :: [LispVal] -> IOThrowsError LispVal
readProc [] = readProc [Port stdin]
readProc [Port port] = (liftIO $ hGetLine port) >>= liftThrows . readExpr

writeProc :: [LispVal] -> IOThrowsError LispVal
writeProc [obj] = writeProc [obj, Port stdout]
writeProc [obj, Port port] = liftIO $ hPrint port obj >> (pure $ Bool True)

readContents :: [LispVal] -> IOThrowsError LispVal
readContents [String filename] = liftM String $ liftIO $ readFile filename

load :: String -> IOThrowsError [LispVal]
load filename = (liftIO $ readFile filename) >>= liftThrows . readExprList

readAll :: [LispVal] -> IOThrowsError LispVal
readAll [String filename] = liftM List $ load filename

primitiveBindings :: IO Env
primitiveBindings =
    nullEnv
        >>= ( flip bindVars
                $ map (makeFunc IOFunc) ioPrimitives
                ++ map (makeFunc PrimitiveFunc) primitives
            )
  where
    makeFunc constructor (var, func) = (var, constructor func)

unaryOp :: (LispVal -> LispVal) -> [LispVal] -> ThrowsError LispVal
unaryOp f [v] = pure $ f v
unaryOp f m = throwError $ NumArgs 1 m

symbolp, numberp, stringp :: LispVal -> LispVal
symbolp (Atom _) = Bool True
symbolp _ = Bool False
numberp (Number _) = Bool True
numberp _ = Bool False
stringp (String _) = Bool True
stringp _ = Bool False

numericBinop :: (Integer -> Integer -> Integer) -> [LispVal] -> ThrowsError LispVal
numericBinop op [] = throwError $ NumArgs 2 []
numericBinop op single@[] = throwError $ NumArgs 2 single
numericBinop op params = mapM unpackNum params >>= return . Number . foldl1 op

boolBinop :: (LispVal -> ThrowsError a) -> (a -> a -> Bool) -> [LispVal] -> ThrowsError LispVal
boolBinop unpacker op args =
    if length args /= 2
        then throwError $ NumArgs 2 args
        else do
            left <- unpacker (head args)
            right <- unpacker (head $ tail args)
            pure $ Bool $ left `op` right

numBoolBinop = boolBinop unpackNum
strBoolBinop = boolBinop unpackStr
boolBoolBinop = boolBinop unpackBool

unpackNum :: LispVal -> ThrowsError Integer
unpackNum (Number n) = return n
unpackNum (String n) =
    let parsed = reads n :: [(Integer, String)]
     in if null parsed
            then throwError $ TypeMismatch "number" $ String n
            else return $ fst $ head parsed
unpackNum (List [n]) = unpackNum n
unpackNum notNum = throwError $ TypeMismatch "number" notNum

unpackStr :: LispVal -> ThrowsError String
unpackStr (String s) = pure s
unpackStr (Number s) = pure $ show s
unpackStr (Bool s) = pure $ show s
unpackStr notString = throwError $ TypeMismatch "string" notString

unpackBool :: LispVal -> ThrowsError Bool
unpackBool (Bool b) = pure b
unpackBool notBool = throwError $ TypeMismatch "boolean" notBool

unpackEquals :: LispVal -> LispVal -> Unpacker -> ThrowsError Bool
unpackEquals arg1 arg2 (AnyUnpacker unpacker) =
    do
        unpacked1 <- unpacker arg1
        unpacked2 <- unpacker arg2
        pure $ unpacked1 == unpacked2
        `catchError` const (pure False)

equal :: [LispVal] -> ThrowsError LispVal
equal [arg1, arg2] = do
    primitiveEqual <-
        or
            <$> mapM
                (unpackEquals arg1 arg2)
                [AnyUnpacker unpackNum, AnyUnpacker unpackStr, AnyUnpacker unpackBool]
    eqvEquals <- eqv [arg1, arg2]
    pure $ Bool (primitiveEqual || let (Bool x) = eqvEquals in x)
equal badArgList = throwError $ NumArgs 2 badArgList

makeFunc varargs env param bo = pure $ Func (map showVal param) varargs bo env
makeNormalFunc = makeFunc Nothing
makeVarArgs = makeFunc . Just . showVal

flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

evalString :: Env -> String -> IO String
evalString env expr = runIOThrows $ fmap show $ liftThrows (readExpr expr) >>= eval env

evalAndPrint :: Env -> String -> IO ()
evalAndPrint env expr = evalString env expr >>= putStrLn

until_ :: (Monad m) => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ predicate prompt action = do
    result <- prompt
    if predicate result
        then pure ()
        else action result >> until_ predicate prompt action

runOne :: [String] -> IO ()
runOne args = do
    env <- primitiveBindings >>= flip bindVars [("args", List $ map String $ drop 1 args)]
    (runIOThrows $ liftM show $ eval env (List [Atom "load", String (head args)]))
        >>= hPutStrLn stderr

runRepl :: IO ()
runRepl = primitiveBindings >>= until_ (== "(quit)") (readPrompt "> ") . evalAndPrint

nullEnv :: IO Env
nullEnv = newIORef []

main :: IO ()
main = do
    args <- getArgs
    if null args then runRepl else runOne args
