{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import System.Exit
import System.Environment
import System.Process
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.List (intersperse)
import Data.Void
import Data.Char

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr

data CustomParseError = InvalidBuiltin Text
  deriving (Eq, Ord)

instance ShowErrorComponent CustomParseError where
  showErrorComponent (InvalidBuiltin b) =
    "`$$" ++ (T.unpack b) ++ "` is not a valid builtin"

type Parser = Parsec CustomParseError Text

data Program t = Program (Expr t)
  deriving Show

data Builtin = BAdd
    deriving Show
data Expr t = EInt Integer
            | EBuiltin Builtin
            | EIdent t Text
            | EApp t (Expr t) [Expr t]
    deriving Show

type UProgram = Program ()
type UExpr    = Expr ()

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "(--" "--)")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

pIdent' :: Parser Text
pIdent' = try $ do
  T.cons <$> (letterChar <|> char '_')
         <*> (takeWhileP Nothing $ \c -> c == '_' || isAlphaNum c)

pIdent :: Parser Text
pIdent = lexeme pIdent'

pInteger :: Parser Integer
pInteger = lexeme L.decimal

pBuiltin :: Parser Builtin
pBuiltin = try $ do
  o <- getOffset
  string "$$"
  x <- pIdent
  case x of
    "add" -> return BAdd
    _     -> do
      setOffset o
      customFailure $ InvalidBuiltin x

pExpr0 :: Parser UExpr
pExpr0 =  (parens pExpr1)
      <|> (EInt <$> pInteger)
      <|> ((EIdent ()) <$> pIdent)
      <|> (EBuiltin <$> pBuiltin)

pExpr1 :: Parser UExpr
pExpr1 = do
  e <- pExpr0
  es <- many pExpr0
  return $
    case es of
      [] -> e
      _  -> EApp () e es

pExpr :: Parser UExpr
pExpr = pExpr1

pProgram :: Parser UProgram
pProgram = Program <$> (sc *> pExpr <* eof)

emitProgram :: Show a => Program a -> Text
emitProgram (Program x) = T.concat
  [ "#include <stdio.h>\n\n\
    \int inc(int x) { return x + 1; }\n\n\
    \int main(int argc, const char** argv) {\n\
    \  printf(\"Result: %d\\n\", ", emitExpr x ,");\n\
    \  return 0;\n\
    \}\n"]
  where
    emitExpr :: Show a => Expr a -> Text
    emitExpr (EInt x) = T.pack $ show x
    emitExpr (EIdent _ x) = x
    emitExpr (EApp _ (EBuiltin b) [x, y]) =
      case b of
        BAdd -> T.concat [ "(", emitExpr x, " + ", emitExpr y, ")" ]
    emitExpr (EApp _ e es) =
      T.concat $ [(emitExpr e), "("] ++ (intersperse ", " $ map emitExpr es) ++ [")"]
    emitExpr x = error $ "Unsuported expression: " ++ (show x)

compileAndRun :: String -> IO ()
compileAndRun f = do
  src <- TIO.readFile f
  case parse pProgram f src of
    Left err -> do
      putStrLn $ errorBundlePretty err
      exitFailure
    Right ast -> do
      let outF = f ++ ".c"
      let out = emitProgram ast
      TIO.writeFile outF out
      callProcess "tcc/tcc.exe" ["-I", "./tcc/include", "-run", outF]

main :: IO ()
main = do
  args <- getArgs
  case args of
    [f] -> compileAndRun f
    _   -> error "Expected a single input file-name"
