module Fy.Typing
  ( runTyping, unify, realize, instanciate, generalize
  , infer
  ) where


import Fy.Types
import Fy.Ast

import Prelude hiding (lookup, lines)
import qualified Data.Set as S
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Control.Monad (when)
import Control.Monad.State
import Control.Monad.Except
import Data.Graph (stronglyConnComp, SCC(..))
import qualified Data.HashMap.Strict as M

data TypingSt = TypingSt { nextId       :: Int
                         , currentSubst :: Subst
                         , env          :: Env }

data TypingError = UnificationError Type Type
                 | OccursCheck
                 | UndefinedVar Ident
                 | InvalidRecursion (NonEmpty Ident)
                 deriving (Show)

type Typing = StateT TypingSt (Except TypingError)

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

introTypeConses :: TypeDef -> Typing ()
introTypeConses (TypeDef _ (TBCType _)) = return ()
introTypeConses (TypeDef t (TBConses cs)) = mapM_ (introTypeCons (TCons t [])) cs

introTypeCons :: Type -> TypeCons -> Typing ()
introTypeCons t (TypeCons c ts) =
  let ct = case ts of
             [] -> t
             _ -> TFun ts t
  in modify (\s -> s { env = M.insert c (MonoType ct) $ env s })


inferFunction :: UFunction -> Typing TFunction
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

inferWithSccLocals :: [SCC (Local ())] -> UExpr -> [Local Type] -> Typing ([Local Type], TExpr)
inferWithSccLocals [] e ls' = do
  e' <- inferExpr e
  return (reverse ls', e')
inferWithSccLocals ((NECyclicSCC xs):_) _ _ = throwError $ InvalidRecursion $ NE.map lName xs
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

typeOfName :: Ident -> Typing Type
typeOfName x = lookup x >>= instanciate

litType :: Lit -> Typing Type
litType (LInt _) = return tInt
litType LUnit = return tUnit

inferExpr :: UExpr -> Typing TExpr
inferExpr (ELit _ l) = do
  t <- litType l
  return $ ELit t l
inferExpr (ELocal _ x) = (\t -> ELocal t x) <$> (typeOfName x)
inferExpr (EGlobal _ x) = (\t -> EGlobal t x) <$> (typeOfName x)
inferExpr (ECons _ x) = (\t -> ECons t x) <$> (typeOfName x)
inferExpr e@(EIdent _ _) = error $ "EIdent found during type inference: " ++ (show e)
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
inferExpr (ECase _ e cs) = do
  e' <- inferExpr e
  cs' <- mapM inferCase cs
  rt <- fresh
  mapM_ (\(Case p _ e0) -> do
            unify (typeOf p) (typeOf e')
            unify (typeOf e0) rt)
    cs'
  return $ ECase rt e' cs'
inferExpr (ETup _ _) = error "Tuples are not supported yet"

inferCase :: UCase -> Typing TCase
inferCase (Case p vs e) = do
  vs' <- mapM (\(v, ()) -> ((,) v) <$> fresh) vs
  scoped (map (\(v, t) -> (v, MonoType t)) vs') $ do
    p' <- inferPat p
    e' <- inferExpr e
    return $ Case p' vs' e'

inferPat :: UPat -> Typing TPat
inferPat (PHole ()) = PHole <$> fresh
inferPat (PLit () l) = do
  t <- litType l
  return $ PLit t l
inferPat (PBinding () x) = (\t -> PBinding t x) <$> (typeOfName x)
inferPat (PCons () c ps) = do
  ps' <- mapM inferPat ps
  ct <- typeOfName c
  t <- fresh
  case ps of
    [] -> unify t ct
    _  -> unify ct (TFun (map typeOf ps') t)
  return $ PCons t c ps'

infer :: [TypeDef] -> UFunction -> Either TypingError TFunction
infer tds f = runTyping $ do
    mapM_ introTypeConses tds
    f' <- inferFunction f
    mainTy <- (TFun []) <$> fresh
    fty <- instanciate $ fType f'
    unify mainTy fty
    realize f'
