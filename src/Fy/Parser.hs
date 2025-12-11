module Fy.Parser
  ( ParserErrorBundle
  , parseProgram, parseModule
  ) where


import Fy.Types
import Fy.Ast

import Prelude hiding (lookup, lines, head)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Set as S
import Data.Functor (($>))
import Data.Char
import Data.List (unsnoc, singleton)
import Data.Maybe (fromMaybe)

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec CustomParseError Text

type ParserErrorBundle = ParseErrorBundle Text CustomParseError

data CustomParseError = InvalidBuiltin Ident
                      | ReservedName Ident
  deriving (Eq, Ord)

instance ShowErrorComponent CustomParseError where
  showErrorComponent (InvalidBuiltin b) =
    "`$$" ++ (show b) ++ "` is not a valid builtin"
  showErrorComponent (ReservedName x) =
    "`" ++ (show x) ++ "` is not a valid indetifier, becasue it's a reserved keyword"


sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "(--" "--)")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

pParens :: Parser a -> Parser a
pParens = between (symbol "(") (symbol ")")

keywords :: [Text]
keywords = ["_", "if", "then", "else"]

pIdent' :: Parser Text
pIdent' = try $ do
  o <- getOffset
  x <- T.cons <$> (letterChar <|> char '_')
              <*> (takeWhileP Nothing $ \c -> c == '_' || isAlphaNum c)
  if x `elem` keywords
  then do
      setOffset o
      customFailure $ ReservedName $ mkId x
  else return x

pIdent :: Parser Ident
pIdent = lexeme $ do
  xs <- pIdent' `sepBy1` (string "/")
  case unsnoc xs of
    Just (ns, x) -> return $ Ident x ns Nothing
    _ -> error $ "Empty ident? " ++ (show xs)

pInteger :: Parser Integer
pInteger = lexeme $ L.signed (return ()) L.decimal

pMagic :: (Text -> Maybe a) -> Parser a
pMagic p = try $ do
  o <- getOffset
  x <- string "$$" *> (lexeme pIdent')
  case p x of
    Just r -> return r
    _ -> do
      setOffset o
      customFailure $ InvalidBuiltin $ mkId x

pBuiltin :: Parser Builtin
pBuiltin = pMagic $ \x ->
  case x of
    "add" -> Just BAdd
    "eq"  -> Just BEq
    _     -> Nothing

pLit :: Parser Lit
pLit =  (try $ symbol "(" *> symbol ")" *> (return LUnit))
    <|> (try $ LInt <$> pInteger)

pTermExpr :: Parser UExpr
pTermExpr =  ((ELit ()) <$> pLit)
      <|> pParenTupleOrUnit
      <|> ((EIdent ()) <$> pIdent)
      <|> ((EBuiltin ()) <$> pBuiltin)
      <|> ((EIf ()) <$> ((symbol "if")   *> pCaseExpr)
                    <*> ((symbol "then") *> pCaseExpr)
                    <*> ((symbol "else"  *> pCaseExpr)))
  where
    pParenTupleOrUnit = do
      es <- pParens $ pFullExpr `sepBy1` (symbol ",")
      return $
        case es of
            []  -> ELit () LUnit
            [e] -> e
            _  -> error "Tuples are not supported yet"

pAppExpr :: Parser UExpr
pAppExpr = do
  e <- pTermExpr
  es <- many pTermExpr
  return $
    case es of
      [] -> e
      _  -> EApp () e es

pCaseExpr :: Parser UExpr
pCaseExpr = do
  e <- pAppExpr
  cases <- many pCase
  case cases of
    [] -> return e
    _ -> return $ ECase () e cases
  where
    pCase = (\p e -> Case p [] e) <$> (symbol "|" *> pPat) <*> (symbol "->" *> pAppExpr)

pLetExpr :: Parser UExpr
pLetExpr = do
  e <- pCaseExpr
  bs <- many pBinding
  return $
    case bs of
        [] -> e
        _ -> ELet () bs e

pFullExpr :: Parser UExpr
pFullExpr = pLetExpr

pBinding :: Parser UBinding
pBinding = do
  x    <- symbol "." *> pIdent
  (isV, args) <- (symbol "()" *> (return $ (False, [])))
                  <|> ((\as -> (null as, as)) <$> (many pIdent))
  body <- symbol "=" *> pCaseExpr
  return $
    if isV
    then Binding (MonoType ()) x Private (S.empty) $ Val body
    else Binding (MonoType ()) x Private (S.empty) $
           Fun $ Function x (MonoType ()) (zip args $ repeat ()) Private (S.empty) body

pPat' :: Parser UPat
pPat' =  (symbol "_" *> (return $ PHole ()))
     <|> ((PLit ()) <$> pLit)
     <|> (pParens pPat)
     <|> ((PBinding ()) <$> pIdent)

pPat :: Parser UPat
pPat =  ((PCons ()) <$> pIdent <*> (many pPat'))
    <|> pPat'

pType' :: Parser Type
pType' = pParenOrUnit
      <|> (\x -> TCons x []) <$> pIdent
  where
    pParenOrUnit = do
      mT <- pParens (optional $ pType)
      case mT of
        Nothing -> return tUnit
        Just t -> return t

pType :: Parser Type
pType = do
  args <- pTypeCons `sepBy1` (symbol ",")
  mRet <- optional $ (symbol "->") *> pTypeCons
  case (args, mRet) of
    (_, Just ret) -> return $ TFun args ret
    ([t], _) -> return t
    (_, _)   -> error "Tuples are not supported yet"
  where
    pTypeCons = TCons <$> (pIdent) <*> (many pType')

pTypeDef :: Parser TypeDef
pTypeDef = do
  x <- symbol ":" *> pIdent
  ps <- many ((\tn -> TCons tn []) <$> pIdent)
  b <- optional $ symbol "=" >> pDefOrCType
  return $ TypeDef x ps $ fromMaybe (TBConses []) b
  where
    pDefOrCType =
      -- TODO: Should be a string
      (TBCType <$> (pMagic (\x -> if x == "ctype" then Just () else Nothing) >> (lexeme pIdent')))
      <|> (TBConses <$> (many (TypeCons <$> (symbol "|" *> pIdent) <*> (many pType'))))

pProgram :: Parser UProgram
pProgram = sc *> (Program <$> (many pTypeDef) <*> pLetExpr) <* eof

data ItemKind = IKImport  PathItem
              | IKExport  PathItem
              | IKTypeDef TypeDef
              | IKFunc    UBinding

pPathItem :: Parser PathItem
pPathItem = do
  (path, head) <- pPathPart
  alias <- pAliasPart
  return $ PathItem path head alias
  where
    pPathPart = lexeme $ do
      root <- pIdent'
      steps <- many (try $ (string "/") *> pIdent')
      head <- optional $  ((string "/*") $> Nothing)
                      <|> (Just <$> ((string "/") *> (pParens $ pIdent `sepBy` (symbol ","))))
      return (root : steps, head)
    pAliasPart = optional $ symbol "=" *> pIdent

pModule :: Parser UModule
pModule = do
  name <- pIdent <?> "Module name"
  items <- many (((symbol "<-" *> ((IKImport <$> pPathItem) `sepBy1` (symbol ","))))
                 <|> ((symbol "->" *> ((IKExport <$> pPathItem) `sepBy1` (symbol ","))))
                 <|> ((singleton . IKTypeDef) <$> pTypeDef)
                 <|> ((singleton . IKFunc) <$> pBinding))
  let (ins, outs, tys, bs) = intoBuckets $ concat items
  return $ Module name ins outs tys bs
  where
    intoBuckets items =
      foldr (\ik (ins, outs, tys, bs) ->
               case ik of
                 IKImport  x -> (x:ins,   outs,   tys,   bs)
                 IKExport  x -> (  ins, x:outs,   tys,   bs)
                 IKTypeDef x -> (  ins,   outs, x:tys,   bs)
                 IKFunc    x -> (  ins,   outs,   tys, x:bs))
        ([], [], [], [])
        items

parseModule :: String -> Text -> Either ParserErrorBundle UModule
parseModule = parse (sc *> pModule <* eof)

parseProgram :: String -> Text -> Either ParserErrorBundle UProgram
parseProgram = parse pProgram
