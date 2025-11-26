{-# LANGUAGE OverloadedStrings, FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveAnyClass, DeriveGeneric, StandaloneDeriving, FunctionalDependencies, MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace (trace, traceStack)
import GHC.Stack (HasCallStack, prettyCallStack, callStack)

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
import Data.Maybe (fromMaybe, maybeToList)
import Data.Char
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

data TypeCons = TypeCons { tdcName :: Ident, tdcMembers :: [Type] }
  deriving (Show)
data TypeBody = TypeBody [TypeCons]
  deriving (Show)
data TypeDef = TypeDef { tdName :: Ident, tdBody :: TypeBody }
  deriving (Show)

data Program t = Program { pTypeDefs :: [TypeDef], pBody :: (Expr t) }
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


data Lit = LInt Integer
         | LUnit
         deriving Show

data Expr t = ELit t Lit
            | ETup t [Expr t]
            | EBuiltin t Builtin
            | EIdent t Ident
            | EApp t (Expr t) [Expr t]
            | ELet t [Local t] (Expr t)
            | EIf t (Expr t) (Expr t) (Expr t)
    deriving (Show, Functor, Foldable)

type TyVar = Int

data Type = TVar TyVar
          | TCons Ident [Type]
          | TFun [Type] Type
          deriving (Eq, Generic)

deriving instance Hashable Type

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
type TypeDefMap = M.HashMap Ident (Maybe TypeBody)

data NamingSt = NamingSt { nstNext   :: Int
                         , nstDepth  :: Int
                         , nstDeps   :: Set Ident
                         , nstTypes  :: TypeDefMap
                         , nstScope  :: NameMap }

data NamingError = UndefinedName Ident
                 | UndefinedType Ident
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

data IRTypeDef = IREnumType Ident [Ident]
               | IRStructType Ident Ident [Type]
               | IRTaggedType Ident [TypeCons]
               deriving Show

data IRLit = IRInt Integer
           | IRVoid
           deriving (Show)

data IRExpr = IRVar Ident
            | IROp Operator [IRExpr]
            | IRCall Ident [IRExpr]
            | IRLit IRLit
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

data IRProgram = IRProgram { irpTypes :: [IRTypeDef], irpFuncs :: [IRFunc] }
            deriving (Show)

data LoweringSt = LoweringSt { lstNext  :: Int
                             , lstFuncs :: [IRFunc]
                             , lstKnownFuncs :: M.HashMap Ident TFunction
                             , lstFuncInsts :: M.HashMap (Ident, Type) IRFunc }

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

suffixId :: Ident -> Text -> Ident
suffixId (Ident x ns i) s = Ident (T.append x s) ns i


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
pExpr0 =  pParenTupleOrUnit
      <|> (((ELit ()) . LInt) <$> pInteger)
      <|> ((EIdent ())        <$> pIdent)
      <|> ((EBuiltin ())      <$> pBuiltin)
      <|> ((EIf ()) <$> ((symbol "if")   *> pExpr1)
                    <*> ((symbol "then") *> pExpr1)
                    <*> ((symbol "else"  *> pExpr1)))
  where
    pParenTupleOrUnit = do
      es <- pParens $ pExpr `sepBy` (symbol ",")
      return $
        case es of
            []  -> ELit () LUnit
            [e] -> e
            es  -> error "Tuples are not supported yet"

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

pType' :: Parser Type
pType' = pParenOrUnit
      <|> (\x -> TCons x []) <$> pIdent
  where
    pParenOrUnit = do
      t <- pParens (optional $ pType)
      case t of
        Nothing -> return tUnit
        Just t -> return t

pType :: Parser Type
pType = do
  args <- pTypeCons `sepBy1` (symbol ",")
  ret <- optional $ (symbol "->") *> pTypeCons
  case (args, ret) of
    (args, Just ret) -> return $ TFun args ret
    ([t], _) -> return t
    (_, _)   -> error "Tuples are not supported yet"
  where
    pTypeCons = TCons <$> (pIdent) <*> (many pType')

pTypeDef :: Parser TypeDef
pTypeDef = do
  symbol ":"
  x <- pIdent
  b <- optional $ do
    symbol "="
    many (TypeCons <$> (symbol "|" *> pIdent) <*> (many pType'))
  return $ TypeDef x $ TypeBody $ fromMaybe [] b

pProgram :: Parser UProgram
pProgram = sc *> (Program <$> (many pTypeDef) <*> pExpr) <* eof

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
      let d = neDepth ne
      if d /= curDepth && d > 0
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

checkType :: Type -> Naming ()
checkType (TVar _) = error "Parametric types are not supported yet"
checkType (TCons x ts) = do
  t <- ((M.lookup x) . nstTypes) <$> get
  case t of
    Nothing -> throwError $ UndefinedType x
    Just _ -> mapM_ checkType ts
checkType (TFun ts t) = (checkType t) >> (mapM_ checkType ts)

checkTypeDef :: TypeDef -> Naming ()
checkTypeDef (TypeDef x (TypeBody cs)) = do
  mapM_ checkAndIntroCons cs
  where
    checkAndIntroCons (TypeCons c ts) = do
      mapM_ checkType ts
      modify (\s -> s { nstScope = M.insert c (NameEntry c 0) $ nstScope s })

checkTypeDefs :: [TypeDef] -> Naming ()
checkTypeDefs tds = do
  modify (\s -> s { nstTypes = M.fromList $ builtins ++ (map (\td -> (tdName td, Just $ tdBody td)) tds) } )
  mapM_ checkTypeDef tds
  where
    builtins = map (\x -> (mkId x, Nothing)) ["int", "()"]

checkProgram :: UProgram -> Naming UFunction
checkProgram (Program tds e) = do
  checkTypeDefs tds
  checkImplicitMain e

-- ======== Typing

instance Typed Expr where
  withType f x@(ELit t _) = f t x
  withType f x@(EIdent t _) = f t x
  withType f x@(EBuiltin t _) = f t x
  withType f x@(EApp t _ _) = f t x
  withType f x@(ELet t _ _) = f t x
  withType f x@(EIf t _ _ _) = f t x

instance FreeVars Type where
    freeVars (TVar x) = S.singleton x
    freeVars (TCons _ ts) = foldMap freeVars ts
    freeVars (TFun ts t) = (foldMap freeVars ts) `S.union` (freeVars t)

instance FreeVars TypeScheme where
  freeVars (MonoType t) = freeVars t
  freeVars (PolyType ts t) = (freeVars t) S.\\ (S.fromList $ ts)

instance FreeVars Env where
  freeVars env = M.foldl' (\vs x -> vs `S.union` (freeVars x)) S.empty env

instance Substitutable Type where
    subst (Subst m) (TVar x) = fromMaybe (TVar x) $ M.lookup x m
    subst s (TCons k ts) = TCons k $ map (subst s) ts
    subst s (TFun ts t)  = TFun (map (subst s) ts) (subst s t)

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

unFn :: Type -> Maybe ([Type], Type)
unFn (TFun ts t) = Just (ts, t)
unFn _ = Nothing

isFnTy :: Type -> Bool
isFnTy (TFun _ _) = True
isFnTy _          = False

instance Show Type where
  show (TVar x) = "'t" ++ show x
  show (TCons x []) = show x
  show (TCons x ts) = "(" ++ (show x) ++ (intercalate " " $ map show ts) ++  ")"
  show (TFun ts t) = "(" ++ (intercalate ", " $ map show ts) ++ " -> " ++ (show t) ++ ")"

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
unify fy@(TFun xs x) fx@(TFun ys y) =
  if length xs == length ys
  then do
    mapM_ (uncurry unify) $ zip xs ys
    unify x y
  else throwError $ UnificationError fx fy
unify x y = throwError $ UnificationError x y

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

infer :: [TypeDef] -> UFunction -> Either TypingError TFunction
infer tds f = runTyping $ do
    mapM_ introTypeConses tds
    f' <- inferFunction f
    mainTy <- (TFun []) <$> fresh
    fty <- instanciate $ fType f'
    unify mainTy fty
    realize f'
  where
    introTypeConses :: TypeDef -> Typing ()
    introTypeConses (TypeDef t (TypeBody cs)) = mapM_ (introTypeCons (TCons t [])) cs
    introTypeCons :: Type -> TypeCons -> Typing ()
    introTypeCons t (TypeCons c ts) =
      let ct = case ts of
                 [] -> t
                 ts -> TFun ts t
      in modify (\s -> s { env = M.insert c (MonoType ct) $ env s })
    inferFunction f = do
      prmTys <- mapM (const fresh) $ fArgs f
      let prms = map (\((x, _), t) -> (x, MonoType t)) $ zip (fArgs f) prmTys
      e' <- scoped prms $ inferExpr $ fBody f
      retTy <- fresh
      unify (typeOf e') retTy
      fty <- realize $ TFun prmTys retTy
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
    inferExpr (ELit _ l) = do
      let t = case l of
                LInt _ -> tInt
                LUnit  -> tUnit
      return $ ELit t l
    inferExpr (EIdent _ x) = do
      t <- lookup x >>= instanciate
      return $ EIdent t x
    inferExpr (EBuiltin _ b) = do
      t <- case b of
             BAdd -> return $ TFun [tInt, tInt] tInt
             BEq  -> (\a -> TFun [a, a] tBool) <$> fresh
      return $ EBuiltin t b
    inferExpr (EApp _ f xs) = do
      f' <- inferExpr f
      xs' <- mapM inferExpr xs
      rt <- fresh
      unify (typeOf f') (TFun (map typeOf xs') rt)
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

runLowering :: Lowering a -> a
runLowering m = fst $ evalRWS m () $
  LoweringSt { lstNext  = 0
             , lstFuncs = []
             , lstFuncInsts = M.empty
             , lstKnownFuncs = M.empty
             }

newVar' :: (Maybe Text) -> Lowering Ident
newVar' t = do
  s <- get
  let x = lstNext s
  modify (\s -> s { lstNext = x + 1 } )
  return $ Ident (fromMaybe "__" t) Nothing (Just x)

newVar :: Lowering Ident
newVar = newVar' Nothing

irDef :: Type -> Ident -> (Maybe IRExpr) -> Lowering ()
irDef t x v =
  if t == tUnit
  then return ()
  else tell [ IRDef t x v ]

lowerLocal :: Local Type -> Lowering ()
lowerLocal l@(Local t x _ (Val e)) = do
  e' <- lowerExpr e
  case t of
    MonoType t -> irDef t x (Just e')
    _ -> error $ "Can't lower a polytype local: " ++ (show l)
lowerLocal (Local _ x _ (Fun f)) =
  modify (\s -> s { lstKnownFuncs = M.insert x f (lstKnownFuncs s) } )

stmts :: Lowering a -> Lowering (a, [IRStmt])
stmts m = censor (const []) $ listen m

filterVoids :: [IRExpr] -> [IRExpr]
filterVoids = filter (\x -> case x of
                              IRLit IRVoid -> False
                              _            -> True)


lowerExpr :: TExpr -> Lowering IRExpr
lowerExpr e =
  if (typeOf e) == tUnit
  then return $ IRLit IRVoid
  else
    case e of
      ELit _ (LInt i) -> return $ IRLit $ IRInt i
      EBuiltin t b -> error $ "Bare operatior: " ++ (show e)
      EIdent t x -> return $ IRVar x
      EApp t (EBuiltin bt b) xs -> do
        xs' <- filterVoids <$> mapM lowerExpr xs
        let o = case b of
                  BAdd -> OpAdd
                  BEq  -> OpEq
        return $ IROp o xs'
      EApp t f xs -> do
        f' <- lowerExpr f
        xs' <- filterVoids <$> mapM lowerExpr xs
        case f' of
          IRVar fx -> do
            fx' <- instanciateFunc fx (typeOf f)
            return $ IRCall fx' xs'
          _ -> error $ "Lowering non-direct calls are not supported yet: " ++ (show $ EApp t f xs)
      ELet t ls e -> do
        mapM_ lowerLocal ls
        lowerExpr e
      EIf t e0 e1 e2 -> do
        r <- newVar' (Just "_phi")
        irDef t r Nothing
        e0' <- lowerExpr e0
        (_, sts1) <- stmts $ do
          e1' <- lowerExpr e1
          tell [ IRSet r e1' ]
        (_, sts2) <- stmts $ do
          e2' <- lowerExpr e2
          tell [ IRSet r e2' ]
        tell [ IRIf e0' sts1 sts2 ]
        return $ IRVar r

lowerBody :: TExpr -> Lowering ()
lowerBody b = do
  r <- lowerExpr b
  tell [ IRReturn r ]

instanciateFunc :: Ident -> Type -> Lowering Ident
instanciateFunc fx ft = do
  let (tArgs, tRet) = case unFn ft of
                        Nothing -> error $ "Non-function type as function head: " ++ (show fx) ++ " : " ++ (show ft)
                        Just r -> r

  st <- get
  case M.lookup (fx, ft) (lstFuncInsts st) of
    Just f -> return $ irfName f
    Nothing -> do
        let f = case M.lookup fx (lstKnownFuncs st) of
                    Nothing -> error $ "Tried to instanciate unknown function: " ++ (show fx)
                    Just f -> f
        case fType f of
          MonoType _ -> do
            f' <- lowerFunction f
            let fx' = irfName f'
            modify (\s -> s { lstFuncInsts = M.insert (fx', ft) f' (lstFuncInsts s) })
            return fx'
          PolyType txs rft -> do
            let mF' = runTyping $ do
                        unify rft ft
                        realize $ f { fType = MonoType ft }
            case mF' of
              Left err -> error $ "Failed to instanciate "
                ++ (show fx) ++ " as " ++ (show ft)
                ++ ": " ++ (show err)
              Right f' -> do
                fx' <- refreshName $ fName f'
                f' <- lowerFunction $ f' { fName = fx' }
                modify (\s -> s { lstFuncInsts = M.insert (fx', ft) f' (lstFuncInsts s) })
                return fx'
  where
    refreshName (Ident x ns i) = do
      let x' = case i of
                Nothing -> x
                Just i -> T.concat [ x, "_", (T.pack $ show i), "_inst__" ]
      (Ident _ _ i') <- newVar
      return $ Ident x' ns i'

lowerFunction :: TFunction -> Lowering IRFunc
lowerFunction f = do
  let (argTs, retT) = case fType f of
                        MonoType fty -> case unFn fty of
                                          Nothing -> error "Type of function isn't a arrow type!"
                                          Just x -> x
                        PolyType _ _ -> error $ "Polymorphic functions are not supported: " ++ (show $ fType f)
  (_, body) <- stmts $ lowerBody $ fBody f
  let f' = IRFunc { irfName  = fName f
                  , irfRetTy = retT
                  , irfArgs  = fArgs f
                  , irfBody  = body }
  modify (\s -> s { lstFuncs = f' : (lstFuncs s) })
  return f'

lowerType :: TypeDef -> IRTypeDef
lowerType (TypeDef _ (TypeBody [])) = error $ "Zero types are not supported yet"
lowerType (TypeDef n (TypeBody [(TypeCons c ts)])) = IRStructType n c ts
lowerType (TypeDef n (TypeBody cs)) =
  if allTags
  then IREnumType n $ reverse variants
  else IRTaggedType n cs
  where
    (allTags, variants) =
      foldl (\(a, vs) (TypeCons v ts) -> (a && (null ts), v : vs)) (True, []) cs

lowerProgram :: [TypeDef] -> TFunction -> Lowering IRProgram
lowerProgram types f = do
  let types' = map lowerType types
  lowerFunction f
  fs <- lstFuncs <$> get
  return $ IRProgram { irpTypes = types', irpFuncs = reverse fs }

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
  line "{"
  r <- indented m
  indent
  emit "}"
  return r

emitProgram :: IRProgram -> Text
emitProgram p = runEmitter $ do
  lines [ "#include <stdio.h>"
        , "#include <stdbool.h>"
        , ""
        ]
  mapM_ (\td -> (emitTypeDef td) >> (emitConses td)) $ irpTypes p
  mapM_ emitFunction $ irpFuncs p
  lines [ "int main(int argc, const char** argv) {"
        , "  printf(\"Result: %d\\n\", __fy_main());"
        , "  return 0;"
        , "}" ]

emitFunction  :: IRFunc -> Emitter ()
emitFunction f = do
    indent
    emitType $ irfRetTy f
    emit " "
    emitIdent $ irfName f
    parens $ do
      let prms = filter ((/= tUnit) . snd) $ irfArgs f
      seperated ", " (\(n, t) -> (emitType t) >> (emit " ") >> (emitIdent n)) prms
    emit " "
    braceBlock $ do
      emitStmts $ irfBody f
    emit "\n\n"

emitStmts :: [IRStmt] -> Emitter ()
emitStmts [] = return ()
emitStmts (s:ss) = indent >> (emitStmt s) >> (emit "\n") >> (emitStmts ss)

emitStmt :: IRStmt -> Emitter ()
emitStmt (IRDef t x mE) = do
  emitType t
  emit " "
  emitIdent x
  mapM_ (\e -> (emit " = ") >> emitExpr e) mE
  emit ";"
emitStmt (IRSet x e) = (emitIdent x) >> (emit " = ") >> (emitExpr e) >> (emit ";")
emitStmt (IREval e) = (emitExpr e) >> (emit ";")
emitStmt (IRReturn e) = (emit "return ") >> (emitExpr e) >> (emit ";")
emitStmt (IRIf e0 sts1 sts2) = do
  emit "if("
  emitExpr e0
  emit ") "
  braceBlock $ emitStmts sts1
  indent >> emit " else "
  braceBlock $ emitStmts sts2

emitExpr :: IRExpr -> Emitter ()
emitExpr (IRVar x) = emitIdent x
emitExpr (IRLit l) =
  case l of
    IRInt x -> emit $ T.pack $ show x
    IRVoid -> emit "/*void*/"
emitExpr (IROp o [x, y]) =
    case o of
        OpAdd -> parens ((emitExpr x) >> (emit " + ") >> (emitExpr y))
        OpEq  -> parens ((emitExpr x) >> (emit " == ") >> (emitExpr y))
emitExpr e@(IROp _ _) = error $ "Invalid operator: " ++ (show e)
emitExpr (IRCall x es) = do
  emitIdent x
  parens $ seperated ", " emitExpr es

emitIdent :: Ident -> Emitter ()
emitIdent (Ident n ns id) = do
  mapM_ (\ns -> tell ["__", ns, "_"]) ns
  emit n
  mapM_ (\id -> tell ["_", T.pack $ show id]) id

emitType :: IRType -> Emitter ()
emitType t@(TVar _) = error $ "Type variable present at emti-stage: " ++ (show t)
emitType (TCons (Ident "int" Nothing Nothing) []) = emit "int"
emitType (TCons (Ident "bool" Nothing Nothing) []) = emit "bool"
emitType (TCons (Ident "()" Nothing Nothing) []) = emit "void"
emitType (TCons x []) = emitIdent x
emitType t = error $ "Unsupported type: " ++ (show t)

emitEnum :: Ident -> [Ident] -> Emitter ()
emitEnum t vs = do
    indent
    emit "typedef enum "
    braceBlock $ do
      mapM_ (\n -> indent >> (emitIdent n) >> line ",") vs
    emit " "
    emitIdent t
    line ";\n"
emitStruct :: Ident -> [Type] -> Emitter ()
emitStruct n ts = do
  indent
  emit "struct "
  braceBlock $ do
      mapM_ (\(i, mt) -> do
              indent
              emitType mt
              emit " "
              emit $ T.pack $ '_' : (show i)
              line ";")
        (zip [0 :: Int ..] ts)
  emit " "
  emitIdent n
  line ";"

emitTypeDef :: IRTypeDef -> Emitter ()
emitTypeDef (IRStructType t c mts) = do
  emit "typedef "
  emitStruct t mts
  line ""
emitTypeDef (IREnumType t variants) = emitEnum t variants
emitTypeDef (IRTaggedType t cs) = do
  let varTy = (t `suffixId` "__variant")
  emitEnum varTy $ map (\(TypeCons v _) -> v) cs
  indent
  emit "typedef struct "
  braceBlock $ do
    indent
    emitIdent varTy
    line " __variant;"
    indent
    emit "union "
    braceBlock $
      mapM_ (\(TypeCons c mts) -> emitStruct c mts) cs
    line ";"
  emit " "
  emitIdent t
  line ";\n"
  where

emitConses :: IRTypeDef -> Emitter ()
emitConses (IREnumType t variants) = do
  mapM_ (\v -> do
            emit "#define MK_"
            emitIdent v
            emit "() "
            emitIdent v
            line "") variants
  line ""
emitConses (IRStructType t c ts) = do
  emit "#define MK_"
  emitIdent c
  let args = map (\(i, _) -> Ident "__arg" Nothing (Just i)) $ zip [0 :: Int ..] ts
  parens $ seperated ", " emitIdent args
  emit " "
  parens $ emitIdent t
  emit " {"
  seperated ", " emitIdent args
  line " }\n"
emitConses (IRTaggedType t cs) = mapM_ emitCons cs >> line ""
  where
    emitCons (TypeCons c ts) = do
      emit "#define MK_"
      emitIdent c
      let args = map (\(i, _) -> Ident "__arg" Nothing (Just i)) $ zip [0 :: Int ..] ts
      parens $ seperated ", " emitIdent args
      emit " "
      parens $ emitIdent t
      emit " {.__variant = "
      emitIdent c
      emit ", ."
      emitIdent c
      emit " = {"
      seperated ", " emitIdent args
      emit "}"
      line "}"

compileAndRun :: String -> IO ()
compileAndRun f = do
  src <- TIO.readFile f
  case parse pProgram f src of
    Left err -> do
      putStrLn $ errorBundlePretty err
      exitFailure
    Right ast' -> do
      let p = ast'
      case runNaming M.empty (checkProgram p) of
        Left err -> putStrLn $ show err
        Right fn -> do
            let types = pTypeDefs p
            case infer types fn of
                Left err -> putStrLn $ show err
                Right ast -> do
                  let ir = runLowering $ lowerProgram types ast
                  let outF = f ++ ".c"
                  let out = emitProgram ir
                  TIO.writeFile outF out
                  callProcess "tcc/tcc.exe" ["-I", "./tcc/include", "-run", outF]

main :: IO ()
main = do
  args <- getArgs
  case args of
    [f] -> compileAndRun f
    _   -> error "Expected a single input file-name"
