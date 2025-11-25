{-# LANGUAGE OverloadedStrings, FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveAnyClass, DeriveGeneric, StandaloneDeriving, FunctionalDependencies, MultiParamTypeClasses #-}
module Main (main) where

import Prelude hiding (lookup, lines)
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
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.List (intersperse, intercalate, partition)
import Data.Maybe (fromMaybe)
import Data.Char
import Debug.Trace (trace)
import Control.Monad (when, foldM)
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.RWS
import Data.Graph (stronglyConnComp, SCC(..))

import qualified Data.HashMap.Strict as M

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

data CustomParseError = InvalidBuiltin Ident
                      | ReservedName Ident
  deriving (Eq, Ord)

instance ShowErrorComponent CustomParseError where
  showErrorComponent (InvalidBuiltin b) =
    "`$$" ++ (show b) ++ "` is not a valid builtin"
  showErrorComponent (ReservedName x) =
    "`" ++ (show x) ++ "` is not a valid indetifier, becasue it's a reserved keyword"

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
  deriving (Show)

data Builtin = BAdd
             | BEq
    deriving Show

data Ident = Ident { idName :: Text
                   , idNamespace :: (Maybe Text)
                   , idSuffix :: (Maybe Int) }
  deriving (Ord, Eq, Generic)

deriving instance Hashable Ident

instance Show Ident where
  show (Ident n ns sf) =
    (fromMaybe "" $ fmap ((++"/") . T.unpack) ns)
    ++ (T.unpack n)
    ++ (fromMaybe "" $ fmap (('$':) . show) sf)

data ValOrFun t = Val (Expr t) | Fun (Function t)
  deriving (Show, Functor, Foldable)

data Local t = Local { lType :: TypeSchemeT t
                     , lName :: Ident
                     , lDeps :: Set Ident
                     , lBody :: ValOrFun t }
  deriving (Show, Foldable, Functor)

data Function t = Function { fName   :: Ident
                           , fType   :: TypeSchemeT t
                           , fArgs   :: [(Ident, t)]
                           , fDeps   :: Set Ident
                           , fBody   :: Expr t }
  deriving (Show, Foldable, Functor)


data Expr t = EInt t Integer
            | EBuiltin t Builtin
            | EIdent t Ident
            | EApp t (Expr t) [Expr t]
            | ELet t [Local t] (Expr t)
            | EIf t (Expr t) (Expr t) (Expr t)
    deriving (Show, Functor, Foldable)

type TyVar = Int

data Type = TVar TyVar
          | TCons Ident [Type]
          deriving Eq

data TypeSchemeT t = MonoType t
                  | PolyType [TyVar] t
                  deriving (Eq, Functor, Foldable)

type TypeScheme = TypeSchemeT Type

data Subst = Subst (M.HashMap Int Type)
  deriving (Show)

type Env = M.HashMap Ident TypeScheme

data TypingSt = TypingSt { nextId       :: Int
                         , currentSubst :: Subst
                         , env          :: Env }

data TypingError = UnificationError Type Type
                 | OccursCheck
                 | UndefinedVar Ident
                 | InvalidRecursion (NonEmpty Ident)
                 deriving (Show)

type Typing = StateT TypingSt (Except TypingError)

data NameEntry = NameEntry { neName  :: Ident
                           , neDepth :: Int }
  deriving Show

type NameMap = M.HashMap Ident NameEntry

data NamingSt = NamingSt { nstNext   :: Int
                         , nstDepth  :: Int
                         , nstDeps   :: Set Ident
                         , nstScope  :: NameMap }

data NamingError = UndefinedName Ident
                 | InvalidCapture Ident
  deriving Show

type Naming = StateT NamingSt (Except NamingError)

type UProgram  = Program ()
type UExpr     = Expr ()
type UFunction = Function ()

type TProgram  = Program Type
type TExpr     = Expr Type
type TFunction = Function Type

type Identation = Int

type Emitter a = RWS Identation [Text] () a

data Operator = OpAdd
              | OpEq
              deriving (Show, Eq)

type IRType = Type

data IRExpr = IRVar Ident
            | IROp Operator
            | IRCall Ident [IRExpr]
            deriving (Show)

data IRStmt = IRDef IRType Ident (Maybe IRExpr)
            | IRSet Ident IRExpr
            | IREval IRExpr
            | IRReturn IRExpr
            | IRIf IRExpr [IRStmt] [IRStmt]
            deriving (Show)

data IRFunc = IRFunc { irfName  :: Ident
                     , irfRetTy :: IRType
                     , irfArgs  :: [(Ident, IRType)]
                     , irfBody  :: [IRStmt] }
            deriving (Show)

data IRProgram = IRProgram { irpFuncs :: [IRFunc] }
            deriving (Show)

data LoweringSt = LoweringSt { lstNext  :: Int
                             , lstFuncs :: [IRFunc]
                             , lstFuncInsts :: M.HashMap (Ident, [Type]) IRFunc }

type Lowering = RWS () [IRStmt] LoweringSt

class (Hashable k, Monad m, MonadError e m) => Context m k v e
    | m -> e, m -> k, m -> v where

  getContext :: m (M.HashMap k v)
  modifyContext :: (M.HashMap k v -> M.HashMap k v) -> m ()
  undefinedVar :: k -> m a

  tryLookup :: k -> m (Maybe v)
  tryLookup k = (M.lookup k) <$> getContext

  lookup :: k -> m v
  lookup k = do
    v <- tryLookup k
    case v of
      Nothing -> undefinedVar k
      Just x -> return x

  insert :: k -> v -> m ()
  insert k v = modifyContext (M.insert k v)

  scoped :: [(k, v)] -> m a -> m a
  scoped kvs m = do
    oldCtx <- getContext
    mapM_  (uncurry insert) kvs
    r <- m
    modifyContext (const oldCtx)
    return r

mkId :: Text -> Ident
mkId x = Ident x Nothing Nothing

isFun :: ValOrFun t -> Bool
isFun (Fun _) = True
isFun _       = False

-- ======== Parser

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "(--" "--)")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

pParens :: Parser a -> Parser a
pParens = between (symbol "(") (symbol ")")

keywords :: [Text]
keywords = ["if", "then", "else"]

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
pIdent = mkId <$> (lexeme pIdent')

pInteger :: Parser Integer
pInteger = lexeme $ L.signed (return ()) L.decimal

pBuiltin :: Parser Builtin
pBuiltin = try $ do
  o <- getOffset
  x <- string "$$" *> pIdent
  case x of
    Ident "add" Nothing Nothing -> return BAdd
    Ident "eq" Nothing Nothing  -> return BEq
    _                           -> do
      setOffset o
      customFailure $ InvalidBuiltin x

pExpr0 :: Parser UExpr
pExpr0 =  (pParens pExpr)
      <|> ((EInt ())     <$> pInteger)
      <|> ((EIdent ())   <$> pIdent)
      <|> ((EBuiltin ()) <$> pBuiltin)
      <|> ((EIf ()) <$> ((symbol "if")   *> pExpr1)
                    <*> ((symbol "then") *> pExpr1)
                    <*> ((symbol "else"  *> pExpr1)))

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
    pBinding = do
      x    <- symbol "." *> pIdent
      args <- many pIdent
      body <- symbol "=" *> pExpr1
      return $
        if null args
        then Local (MonoType ()) x (S.empty) $ Val body
        else Local (MonoType ()) x (S.empty) $
               Fun $ Function x (MonoType ()) (zip args $ repeat ()) (S.empty) body

pExpr :: Parser UExpr
pExpr = pExpr2

pProgram :: Parser UProgram
pProgram = Program <$> (sc *> pExpr <* eof)

-- ======== Naming

instance Context Naming Ident NameEntry NamingError where
  getContext = nstScope <$> get
  modifyContext f = modify (\s -> s { nstScope = f $ nstScope s })
  undefinedVar = throwError . UndefinedName

uniqId :: Ident -> Naming Ident
uniqId (Ident x ns _) = do
  n <- nstNext <$> get
  modify (\s -> s { nstNext = n + 1 })
  return $ Ident x ns (Just n)

block :: Naming a -> Naming (a, Set Ident)
block x = do
  oldSt <- get
  modify (\s -> s { nstDeps = S.empty })
  r <- x
  st <- get
  modify (\s -> s { nstDeps = nstDeps oldSt })
  return (r, nstDeps st)

addDeps :: Ident -> Naming ()
addDeps x = modify (\s -> s { nstDeps = S.insert x (nstDeps s) })

runNaming :: NameMap -> Naming a -> Either NamingError a
runNaming gs n = runExcept (evalStateT n st)
  where
    st = NamingSt { nstNext = 0, nstScope = gs, nstDepth = 0 }

scopedVars' :: [Ident] -> Naming a -> Naming ([Ident], a)
scopedVars' xs m = do
    d <- nstDepth <$> get
    xs' <- mapM uniqId xs
    scoped (map (\(x, x') -> (x, NameEntry x' d)) $ zip xs xs') $ ((,) xs') <$> m

scopedVars :: [Ident] -> Naming a -> Naming a
scopedVars xs m = snd <$> scopedVars' xs m

checkExpr :: UExpr -> Naming UExpr
checkExpr e =
  case e of
    EIdent () x  -> do
      ne <- lookup x
      curDepth <- nstDepth <$> get
      addDeps $ neName ne
      if (neDepth ne) /= curDepth
      then throwError $ InvalidCapture (neName ne)
      else return $ EIdent () (neName ne)
    EApp () f xs -> (EApp ()) <$> (checkExpr f) <*> (mapM checkExpr xs)
    ELet () bs e -> checkLocals bs e
    EIf () e0 e1 e2 -> do
       e0' <- checkExpr e0
       e1' <- checkExpr e1
       e2' <- checkExpr e2
       return $ EIf () e0' e1' e2'
    _ -> return e
  where
    checkLocals :: [Local ()] -> UExpr -> Naming UExpr
    checkLocals ls e = do
      (ls', e') <- scopedVars (map (\(Local { lName = x }) -> x) ls) $ do
        ls' <- mapM checkLocal ls
        e' <- checkExpr e
        return (ls', e')
      return $ ELet () ls' e'
    checkLocal (Local t x _ (Val e)) = do
      (NameEntry x' _) <- lookup x
      (e', deps) <- block $ checkExpr e
      return $ Local t x' deps (Val e')
    checkLocal (Local t x _ (Fun f)) = do
       (NameEntry x' _) <- lookup x
       f <- checkFunction x' (map fst $ fArgs f) (fBody f)
       return $ Local t x' (S.empty) (Fun f)

checkFunction :: Ident -> [Ident] -> UExpr -> Naming UFunction
checkFunction f xs e = do
  oldDepth <- nstDepth <$> get
  modify (\s -> s { nstDepth = oldDepth + 1 })
  (xs', (body, deps)) <- scopedVars' xs $ block (checkExpr e)
  modify (\s -> s { nstDepth = oldDepth })
  return $ Function f (MonoType ()) (map (\x -> (x, ())) xs') deps body

checkImplicitMain :: UExpr -> Naming UFunction
checkImplicitMain e = checkFunction (mkId "__fy_main") [] e

-- ======== Typing

instance Typed Expr where
  withType f x@(EInt t _) = f t x
  withType f x@(EIdent t _) = f t x
  withType f x@(EBuiltin t _) = f t x
  withType f x@(EApp t _ _) = f t x
  withType f x@(ELet t _ _) = f t x
  withType f x@(EIf t _ _ _) = f t x

instance FreeVars Type where
    freeVars (TVar x) = S.singleton x
    freeVars (TCons _ ts) = foldMap freeVars ts

instance FreeVars TypeScheme where
  freeVars (MonoType t) = freeVars t
  freeVars (PolyType ts t) = (freeVars t) S.\\ (S.fromList $ ts)

instance FreeVars Env where
  freeVars env = M.foldl' (\vs x -> vs `S.union` (freeVars x)) S.empty env

instance Substitutable Type where
    subst (Subst m) (TVar x) = fromMaybe (TVar x) $ M.lookup x m
    subst s (TCons k ts) = TCons k $ map (subst s) ts

instance Substitutable (Expr Type) where
  subst s x = fmap (subst s) x

instance Substitutable TypeScheme where
  subst s (MonoType t) = MonoType $ subst s t
  -- ASSUMPTION: All the type variables are fresh and shouldn't exist in s
  subst s (PolyType ts t) = PolyType ts $ subst s t

instance Substitutable (ValOrFun Type) where
  subst s (Val v) = Val $ subst s v
  subst s (Fun f) = Fun $ subst s f

instance Substitutable (Local Type) where
  subst s l = l { lType = subst s $ lType l
                , lBody = subst s $ lBody l }

instance Substitutable TFunction  where
  subst s f = f { fBody = subst s $ fBody f
                , fType = subst s $ fType f
                , fArgs = map (\(x, t) -> (x, subst s t)) $ fArgs f }

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

tBool :: Type
tBool = TCons (mkId "bool") []

tUnit :: Type
tUnit = TCons (mkId "()") []

tFn :: [Type] -> Type -> Type
tFn [] y = TCons (mkId "->") [tUnit, y]
tFn ts y = foldr (\t r -> TCons (mkId "->") [t, r]) y ts

unFn :: Type -> Maybe ([Type], Type)
unFn (TCons (Ident "->" Nothing Nothing) [x, y]) = Just $ helper [x] y
  where
    helper args (TCons (Ident "->" Nothing Nothing) [arg, tail]) = helper (arg:args) tail
    helper args ret = (reverse args, ret)
unFn _ = Nothing

instance Show Type where
  show (TVar x) = "'t" ++ show x
  show (TCons (Ident "->" Nothing Nothing) [x, y]) =  "(" ++ (show x) ++ " -> " ++ (show y) ++ ")"
  show (TCons x ts) = "(" ++ (show x) ++ (intercalate " " $ map show ts) ++  ")"

instance Show a => Show (TypeSchemeT a)  where
  show (MonoType t) = show t
  show (PolyType ts t) = "forall " ++ (intercalate " " $ map (show . TVar) ts) ++ " . " ++ (show t)

(=:=) :: TyVar -> Type -> Typing ()
(=:=) x t' = do
  st <- get
  let sub = currentSubst st
  let t = sub `subst` t'
  when (x `elem` (freeVars t)) $ throwError OccursCheck
  let x' = sub `subst` (TVar x)
  let sub = currentSubst st
  case x' of
    TVar y | x == y -> return ()
    _ -> x' `unify` t
  modify (\s -> s { currentSubst = addSubst x t $ currentSubst s })

instance Context Typing Ident TypeScheme TypingError where
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

realize :: Substitutable a => a -> Typing a
realize x = do
  ss <- currentSubst <$> get
  return $ subst ss x

instanciate :: TypeScheme -> Typing Type
instanciate (MonoType t) = return t
instanciate (PolyType ts t) = do
  ss <- mapM (\tx -> ((,) tx) <$> fresh) ts
  return $ subst (Subst $ M.fromList ss) t

generalize :: Type -> Typing TypeScheme
generalize t = do
  outerFrees <- (freeVars . env) <$> get
  let frees = freeVars t
  let innerFrees = S.toList $ frees S.\\ outerFrees
  case innerFrees of
    [] -> return $ MonoType t
    _  -> return $ PolyType innerFrees t

runTyping :: Typing a -> Either TypingError a
runTyping t = runExcept $ evalStateT t defaultTypingSt

infer :: UFunction -> Either TypingError TFunction
infer f = runTyping $ do
    f' <- inferFunction f
    mainTy <- (tFn []) <$> fresh
    fty <- instanciate $ fType f'
    unify mainTy fty
    realize f'
  where
    inferFunction f = do
      prmTys <- mapM (const fresh) $ fArgs f
      let prms = map (\((x, _), t) -> (x, MonoType t)) $ zip (fArgs f) prmTys
      e' <- scoped prms $ inferExpr $ fBody f
      retTy <- fresh
      unify (typeOf e') retTy
      fty <- realize $ tFn prmTys retTy
      fty' <- generalize fty
      realize $ Function { fName = fName f
                        , fType = fty'
                        , fArgs = zip (map fst $ fArgs f) prmTys
                        , fDeps   = fDeps f
                        , fBody   = e' }
    inferWithSccLocals [] e ls' = do
      e' <- inferExpr e
      return (reverse ls', e')
    inferWithSccLocals ((NECyclicSCC xs):ls) e ls' = throwError $ InvalidRecursion $ NE.map lName xs
    inferWithSccLocals ((AcyclicSCC l):ls) e ls' = do
      (vof, t') <- case lBody l of
          Val e0 -> do
              e0' <- inferExpr e0
              t <- realize $ typeOf e0'
              t' <- generalize t
              return (Val e0', t')
          Fun f  -> do
            f' <- inferFunction f
            return (Fun f', fType f')
      scoped [(lName l, t')] $ inferWithSccLocals ls e ((Local t' (lName l) (lDeps l) vof):ls')
    inferExpr (EInt _ x) = return $ EInt tInt x
    inferExpr (EIdent _ x) = do
      t <- lookup x >>= instanciate
      return $ EIdent t x
    inferExpr (EBuiltin _ b) = do
      t <- case b of
             BAdd -> return $ tFn [tInt, tInt] tInt
             BEq  -> (\a -> tFn [a, a] tBool) <$> fresh
      return $ EBuiltin t b
    inferExpr (EApp _ f xs) = do
      f' <- inferExpr f
      xs' <- mapM inferExpr xs
      rt <- fresh
      unify (typeOf f') (tFn (map typeOf xs') rt)
      return $ EApp rt f' xs'
    inferExpr (EIf _ e0 e1 e2) = do
      e0' <- inferExpr e0
      e1' <- inferExpr e1
      e2' <- inferExpr e2
      unify (typeOf e0') tBool
      unify (typeOf e1') (typeOf e2')
      return $ EIf (typeOf e1') e0' e1' e2'
    inferExpr (ELet _ ls e) = do
      let sccs = stronglyConnComp $ map (\l -> (l, lName l, S.toList $ lDeps l)) ls
      (ls', e') <- inferWithSccLocals sccs e []
      return $ ELet (typeOf e') ls' e'

-- ======== Lowering

-- runLowering :: Lowering a -> a
-- runLowering m = fst $ evalRWS m () $
--   LoweringSt { lstNext  = 0
--              , lstFuncs = []
--              , lstFuncInsts = M.empty }

-- newVar' :: (Maybe Text) -> Lowering Ident
-- newVar' t = do
--   s <- get
--   let x = lstNext s
--   modify (\s -> s { lstNext = x + 1 } )
--   return $ Ident (fromMaybe "__" t) Nothing (Just x)

-- newVar :: Lowering Ident
-- newVar = newVar' Nothing

-- -- lowerExpr :: TExpr -> Lowering ()
-- -- lowerExpr e =
-- --   case e of
-- --     EInt _ i ->

-- lowerBody :: TExpr -> Lowering ()
-- lowerBody b = do
--   r <- lowerExpr

-- lowerFunction :: TFunction -> Lowering IRFunc
-- lowerFunction f = do
--   let (lFuns, lVars) = partition (\(Local _ _ _ k) -> isFun k) $ fLocals f
--   mapM_ (\(Local _ _ _ (Fun f0)) -> lowerFunction f0) lFuns
--   let (argTs, retT) = case fType f of
--                         MonoType fty -> case unFn fty of
--                                           Nothing -> error "Type of function isn't a arrow type!"
--                                           Just x -> x
--                         PolyType _ _ -> error $ "Polymorphic functions are not supported: " ++ (show $ fType f)
--   (_, body) <- listen $ lowerBody $ fBody f
--   return $ IRFunc { irfName  = fName f
--                   , irfRetTy = retT
--                   , irfArgs  = fArgs f
--                   , irfBody  = body }

-- lowerProgram :: TFunction -> Lowering IRProgram
-- lowerProgram f = do
--   lowerFunction f
--   fs <- lstFuncs <$> get
--   return $ IRProgram { irpFuncs = fs }

-- ======== Emitting

runEmitter :: Emitter () -> Text
runEmitter m = T.concat $ snd $ evalRWS m 0 ()

indented :: Emitter a -> Emitter a
indented m = local (+1) m

indent :: Emitter ()
indent = do
  d <- ask
  emit $ T.replicate d "  "

line :: Text -> Emitter ()
line l = tell [ l, "\n" ]

lines :: [Text] -> Emitter ()
lines ls = do
  tell $ intersperse "\n" ls
  tell ["\n"]

around :: Text -> Text -> Emitter a -> Emitter a
around o c m = do
  emit o
  r <- m
  emit c
  return r

parens :: Emitter a -> Emitter a
parens = around "(" ")"

seperated :: Text -> (a -> Emitter ()) -> [a] -> Emitter ()
seperated _ _ []  = return ()
seperated _ f [x] = f x
seperated sep f (x0:x1:xs) = (f x0) >> (emit sep) >> (seperated sep f (x1:xs))

emit :: Text -> Emitter ()
emit x = tell [ x ]

braceBlock :: Emitter a -> Emitter a
braceBlock m = do
  indent
  line "{"
  r <- indented m
  indent
  line "}"
  return r

emitProgram :: TFunction -> Text
emitProgram f = runEmitter $ do
  lines [ "#include <stdio.h>"
        , "#include <stdbool.h>"
        , ""
        , "int inc(int x) { return x + 1; }\n"
        ]
  emitFunction f
  lines [ "int main(int argc, const char** argv) {"
        , "  printf(\"Result: %d\\n\", __fy_main());"
        , "  return 0;"
        , "}" ]

emitFunction  :: TFunction -> Emitter ()
emitFunction f = do
    let (argTs, retT) = case fType f of
                            MonoType fty -> case unFn fty of
                                                Nothing -> error "Type of function isn't a arrow type!"
                                                Just x -> x
                            PolyType _ _ -> error $ "Polymorphic functions are not supported: " ++ (show $ fType f)
    indent
    emitType retT
    emit " "
    emitIdent $ fName f
    parens $ do
      let prms = filter ((/= tUnit) . snd) $ fArgs f
      seperated ", " (\(n, t) -> (emitType t) >> (emit " ") >> (emitIdent n)) prms
    braceBlock $ do
      indent
      emit "return "
      emitExpr $ fBody f
      line ";"
    emit "\n"

emitExpr :: TExpr -> Emitter ()
emitExpr e = do
   -- tell ["/* ", T.pack (show $ typeOf e), " */"]
   emitExpr' e
emitExpr' :: TExpr -> Emitter ()
emitExpr' (EInt _ x) = emit $ T.pack $ show x
emitExpr' (EIdent _ x) = emitIdent x
emitExpr' (EApp _ (EBuiltin _ b) [x, y]) =
    case b of
        BAdd -> parens ((emitExpr x) >> (emit " + ") >> (emitExpr y))
        BEq  -> parens ((emitExpr x) >> (emit " == ") >> (emitExpr y))
emitExpr' (EApp _ e es) = do
  emitExpr e
  parens $ seperated ", " emitExpr es
emitExpr' (EIf _ e0 e1 e2) = do
  parens $ do
    emitExpr e0
    emit " ? "
    emitExpr e1
    emit " : "
    emitExpr e2
emitExpr' (ELet t ls e) =
  braceBlock $ do
    mapM (\l ->
            case l of
              Local (MonoType t) n _ (Val e) -> do
                indent
                emitType t
                emit " "
                emitIdent n
                emit " = "
                emitExpr e
                line ";"
              Local _ _ _ (Fun f) -> emitFunction f)
         ls
    emitExpr e


emitIdent :: Ident -> Emitter ()
emitIdent (Ident n ns id) = do
  mapM_ (\ns -> tell ["__", ns, "_"]) ns
  emit n
  mapM_ (\id -> tell ["_", T.pack $ show id]) id

emitType :: Type -> Emitter ()
emitType t@(TVar _) = error $ "Type variable present at emti-stage: " ++ (show t)
emitType (TCons (Ident "int" Nothing Nothing) []) = emit "int"
emitType (TCons (Ident "bool" Nothing Nothing) []) = emit "bool"
emitType (TCons (Ident "()" Nothing Nothing) []) = emit "void"
emitType t = error $ "Unsupported type: " ++ (show t)

compileAndRun :: String -> IO ()
compileAndRun f = do
  src <- TIO.readFile f
  case parse pProgram f src of
    Left err -> do
      putStrLn $ errorBundlePretty err
      exitFailure
    Right ast' -> do
      let Program e = ast'
      case runNaming M.empty (checkImplicitMain e) of
        Left err -> putStrLn $ show err
        Right fn ->
            case infer fn of
                Left err -> putStrLn $ show err
                Right ast -> do
                    putStrLn $ show ast
                    -- putStrLn $ show $ runLowering $ lowerProgram ast
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
