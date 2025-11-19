{-# LANGUAGE OverloadedStrings, FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveAnyClass, DeriveGeneric, StandaloneDeriving, FunctionalDependencies, MultiParamTypeClasses #-}
module Main (main) where

import Prelude hiding (lookup)
import GHC.Generics (Generic)
import System.Exit
import System.Environment
import System.Process hiding (env)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Set as S
import Data.Hashable (Hashable)
import Data.Set (Set)
import Data.List (intersperse, intercalate)
import Data.Maybe (fromMaybe)
import Data.Char
import Control.Monad (when)
import Control.Monad.State
import Control.Monad.Except
import Data.Graph (stronglyConnComp)

import qualified Data.HashMap.Strict as M

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

data CustomParseError = InvalidBuiltin Ident
  deriving (Eq, Ord)

instance ShowErrorComponent CustomParseError where
  showErrorComponent (InvalidBuiltin b) =
    "`$$" ++ (show b) ++ "` is not a valid builtin"

type Parser = Parsec CustomParseError Text

class Functor a => Typed a where
  withType :: (Type -> a Type -> x) -> a Type -> x
  typeOf :: (a Type) -> Type
  typeOf = withType (\t _ -> t)

class FreeVars a where
  freeVars :: a -> Set TyVar

class Substitutable a where
  subst :: Subst -> a -> a

data Program t = Program (Expr t)
  deriving (Show, Functor)

data Builtin = BAdd
    deriving Show

data Ident = Ident { idName :: Text
                   , idNamespace :: (Maybe Text)
                   , idSuffix :: (Maybe Integer) }
  deriving (Ord, Eq, Generic)

deriving instance Hashable Ident

instance Show Ident where
  show (Ident n ns sf) =
    (fromMaybe "" $ fmap ((++"/") . T.unpack) ns)
    ++ (T.unpack n)
    ++ (fromMaybe "" $ fmap (('$':) . show) sf)

data Binding t = Binding t Ident [Ident] (Set Ident) (Expr t)
    deriving (Show, Functor, Foldable)

data Expr t = EInt t Integer
            | EBuiltin t Builtin
            | EIdent t Ident
            | EApp t (Expr t) [Expr t]
            | ELet t [Binding t] (Expr t)
    deriving (Show, Functor, Foldable)

type TyVar = Int

data Type = TVar TyVar
          | TCons Ident [Type]
          deriving Eq

data Subst = Subst (M.HashMap Int Type)

type Env = M.HashMap Ident Type

data TypingSt = TypingSt { nextId       :: Int
                         , currentSubst :: Subst
                         , env          :: Env }

data TypingError = UnificationError Type Type
                 | OccursCheck
                 | UndefinedVar Ident
                 deriving (Show)

type Typing = StateT TypingSt (Except TypingError)

type UProgram = Program ()
type UExpr    = Expr ()

type TProgram = Program Type
type TExpr    = Expr Type

data NameEntry = NameEntry { neName  :: Ident
                           , neDepth :: Int
                           , neDeps  :: Set Ident }

type NameMap = M.HashMap Ident NameEntry

data NamingSt = NamingSt { nstNext  :: Int
                         , nstDepth :: Int
                         , nstScope :: NameMap }

data NamingError = UndefinedName Ident
                 | InvalidCapture Ident

type Naming = StateT NamingSt (Except NamingError)

data ValOrFun t = Val (Expr t) | Fun (Function t)

data Local t = Local { lName :: Ident
                     , lDeps :: Set Ident
                     , lBody :: ValOrFun t }

data Function t = Function { fName   :: Ident
                           , fType   :: t
                           , fArgs   :: [(Ident, t)]
                           , fLocals :: M.HashMap Ident (Local t)
                           , fBody   :: Expr t }

class (Hashable k, Monad m, MonadError e m) => Context m k v e
    | m -> e, m -> k, m -> v where

  getContext :: m (M.HashMap k v)
  modifyContext :: (M.HashMap k v -> M.HashMap k v) -> m ()
  undefinedVar :: k -> m a

  lookup :: k -> m v
  lookup k = do
    v <- (M.lookup k) <$> getContext
    case v of
      Nothing -> undefinedVar k
      Just x -> return x

  insert :: k -> v -> m ()
  insert k v = modifyContext (M.insert k v)

  scoped :: k -> v -> m a -> m a
  scoped k v m = do
    oldCtx <- getContext
    insert k v
    r <- m
    modifyContext (const oldCtx)
    return r

mkId :: Text -> Ident
mkId x = Ident x Nothing Nothing

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

pIdent :: Parser Ident
pIdent = mkId <$> (lexeme pIdent')

pInteger :: Parser Integer
pInteger = lexeme L.decimal

pBuiltin :: Parser Builtin
pBuiltin = try $ do
  o <- getOffset
  x <- string "$$" *> pIdent
  case x of
    Ident "add" Nothing Nothing -> return BAdd
    _                           -> do
      setOffset o
      customFailure $ InvalidBuiltin x

pExpr0 :: Parser UExpr
pExpr0 =  (parens pExpr1)
      <|> ((EInt ()) <$> pInteger)
      <|> ((EIdent ()) <$> pIdent)
      <|> ((EBuiltin ()) <$> pBuiltin)

pExpr1 :: Parser UExpr
pExpr1 = do
  e <- pExpr0
  es <- many pExpr0
  return $
    case es of
      [] -> e
      _  -> EApp () e es

pExpr2 :: Parser UExpr
pExpr2 = do
  e <- pExpr1
  bs <- many pBinding
  return $
    case bs of
        [] -> e
        _ -> ELet () bs e
  where
    pBinding = (Binding ()) <$> (symbol "." *> pIdent) <*> (many pIdent) <*> (return $ S.empty) <*> (symbol "=" *> pExpr1)

pExpr :: Parser UExpr
pExpr = pExpr2

pProgram :: Parser UProgram
pProgram = Program <$> (sc *> pExpr <* eof)

instance Context Naming Ident NameEntry NamingError where
  getContext = nstScope <$> get
  modifyContext f = modify (\s -> s { nstScope = f $ nstScope s })
  undefinedVar = throwError . UndefinedName

runNaming :: NameMap -> Naming a -> Either NamingError a
runNaming gs n = runExcept (evalStateT n st)
  where
    st = NamingSt { nstNext = 0, nstScope = gs, nstDepth = 0 }

instance Typed Binding where
  withType f x@(Binding t _ _ _ _) = f t x

instance Typed Expr where
  withType f x@(EInt t _) = f t x
  withType f x@(EIdent t _) = f t x
  withType f x@(EBuiltin t _) = f t x
  withType f x@(EApp t _ _) = f t x
  withType f x@(ELet t _ _) = f t x

instance FreeVars Type where
    freeVars (TVar x) = S.singleton x
    freeVars (TCons _ ts) = foldMap freeVars ts

instance FreeVars (Expr Type) where
  freeVars = foldMap freeVars

instance Substitutable Type where
    subst (Subst m) (TVar x) = fromMaybe (TVar x) $ M.lookup x m
    subst _ x = x

instance Functor a => Substitutable (a Type) where
  subst s x = fmap (subst s) x

defaultTypingSt :: TypingSt
defaultTypingSt = TypingSt { nextId = 0
                           , currentSubst = Subst M.empty
                           , env = M.empty }

addSubst :: TyVar -> Type -> Subst -> Subst
addSubst x t (Subst s) = Subst $
  M.insert x t' s'
  where
    t' = (Subst s) `subst` t
    s' = M.map (subst (Subst $ M.singleton  x t')) s

fresh' :: Typing TyVar
fresh' = do
  st <- get
  let x = nextId st
  modify (\s -> s { nextId = x + 1 })
  return x

fresh :: Typing Type
fresh = TVar <$> fresh'

tInt :: Type
tInt = TCons (mkId "int") []

tFn :: [Type] -> Type -> Type
tFn [] y = y
tFn (t:ts) y = TCons (mkId "->") [t, tFn ts y]

instance Show Type where
  show (TVar x) = "'t" ++ show x
  show (TCons (Ident "->" Nothing Nothing) [x, y]) =  "(" ++ (show x) ++ " -> " ++ (show y) ++ ")"
  show (TCons x ts) = "(" ++ (show x) ++ (intercalate " " $ map show ts) ++  ")"

(=:=) :: TyVar -> Type -> Typing ()
(=:=) x t' = do
  st <- get
  let sub = currentSubst st
  let t = sub `subst` t'
  when (x `elem` (freeVars t)) $ throwError OccursCheck
  let x' = sub `subst` (TVar x)
  case x' of
    TVar y | x == y -> return ()
    _ -> x' `unify` t
  modify (\s -> s { currentSubst = addSubst x t sub })

instance Context Typing Ident Type TypingError where
  getContext = env <$> get
  modifyContext f = modify (\s -> s { env = f $ env s })
  undefinedVar = throwError . UndefinedVar

unify :: Type -> Type -> Typing ()
unify (TVar x) y = x =:= y
unify x (TVar y) = y =:= x
unify ty@(TCons x xs) tx@(TCons y ys) =
  if x == y && length xs == length ys
  then mapM_ (uncurry unify) $ zip xs ys
  else throwError $ UnificationError tx ty

runTyping :: Typing a -> Either TypingError a
runTyping t = runExcept $ evalStateT t defaultTypingSt

infer :: UProgram -> Either TypingError TProgram
infer p = runTyping (inferProgram p)
  where
    inferProgram (Program e) = do
      e' <- inferExpr e
      st <- get
      return $ Program (subst (currentSubst st) e')
    inferExpr (EInt _ x) = return $ EInt tInt x
    inferExpr (EIdent _ x) = do
      t <- lookup x
      return $ EIdent t x
    inferExpr (EBuiltin _ b) = do
      let t = case b of
            BAdd -> tFn [tInt, tInt] tInt
      return $ EBuiltin t b
    inferExpr (EApp _ f xs) = do
      f' <- inferExpr f
      xs' <- mapM inferExpr xs
      rt <- fresh
      unify (typeOf f') (tFn (map typeOf xs') rt)
      return $ EApp rt f' xs'
    inferExpr (ELet _ bs e) = do
      (e', bs') <- inferBindings bs e []
      return $ ELet (typeOf e') bs' e'

    inferBindings [] e bs' = do
      e' <- inferExpr e
      return (e', reverse bs')
    inferBindings ((Binding _ x [] _ e0):bs) e1 bs' = do
      e0' <- inferExpr e0
      let t = typeOf e0'
      scoped x t $ inferBindings bs e1 ((Binding t x [] S.empty e0'):bs')
    inferBindings _ _ _ = error $ "Bindings with parameters are not supported yet"



emitProgram :: TProgram -> Text
emitProgram (Program p) = T.concat
  [ "#include <stdio.h>\n\n\
    \int inc(int x) { return x + 1; }\n\n\
    \int main(int argc, const char** argv) {\n\
    \  printf(\"Result: %d\\n\", ", emitExpr p ,");\n\
    \  return 0;\n\
    \}\n"]
  where
    emitExpr :: TExpr -> Text
    emitExpr e = T.concat [ "/* ", T.pack (show $ typeOf e), " */", emitExpr' e ]
    emitExpr' :: TExpr -> Text
    emitExpr' (EInt _ x) = T.pack $ show x
    emitExpr' (EIdent _ x) = T.pack $ show x
    emitExpr' (EApp _ (EBuiltin _ b) [x, y]) =
      case b of
        BAdd -> T.concat [ "(", emitExpr x, " + ", emitExpr y, ")" ]
    emitExpr' (EApp _ e es) =
      T.concat $ [(emitExpr e), "("] ++ (intersperse ", " $ map emitExpr es) ++ [")"]
    emitExpr' (ELet _ bs e) =
      T.concat $ (map emitBinding bs) ++ [emitExpr e]
    emitExpr' x = error $ "Unsuported expression: " ++ (show x)

    emitBinding (Binding t x [] _ e) =
      T.concat [ emitType t, " ", T.pack (show x), " = ", emitExpr e, ";\n" ]
    emitBinding b = error $ "Unsupported binding: " ++ (show b)

    emitType :: Type -> Text
    emitType t@(TVar _) = error $ "Type variable present at emti-stage: " ++ (show t)
    emitType (TCons (Ident "int" Nothing Nothing) []) = "int"
    emitType t = error $ "Unsupported type: " ++ (show t)

compileAndRun :: String -> IO ()
compileAndRun f = do
  src <- TIO.readFile f
  case parse pProgram f src of
    Left err -> do
      putStrLn $ errorBundlePretty err
      exitFailure
    Right ast' ->
      case infer ast' of
        Left err -> putStrLn $ show err
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
