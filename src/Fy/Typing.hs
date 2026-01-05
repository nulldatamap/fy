module Fy.Typing
  ( runTyping, unify, realize, instanciate, generalize
  , infer
  ) where


import Fy.Types
import Fy.Ast

import Prelude hiding (lookup, lines)
import qualified Data.Set as S
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Control.Monad (when)
import Control.Monad.State.Strict
import Control.Monad.Except
import Data.Graph (stronglyConnComp, SCC(..))
import qualified Data.HashMap.Strict as M

data TypingSt = TypingSt { nextId       :: Int
                         , currentSubst :: Subst
                         , env          :: Env }

data TypingError = UnificationError Type Type
                 | OccursCheck TyVar Type
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
  when (x `elem` (freeVars t)) $ throwError $ OccursCheck x t
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
unify (TVar x) (TVar y) | x == y = return ()
unify (TVar x) y = x =:= y
unify x (TVar y) = y =:= x
unify ty@(TCons x xs) tx@(TCons y ys) =
  if x == y && length xs == length ys
  then mapM_ (uncurry unify) $ zip xs ys
  else throwError $ UnificationError tx ty
-- Special rule for nilary functions:
unify (TFun [] x) (TFun [t0] y) | t0 == tUnit = unify x y
unify (TFun [t0] x) (TFun [] y) | t0 == tUnit = unify x y
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
introTypeConses (TypeDef _ _ _ (TBCType _)) = return ()
introTypeConses (TypeDef _ _ _ (TBAlias _)) = return ()
introTypeConses (TypeDef t ps _ (TBConses cs)) = mapM_ (introTypeCons ps (TCons t ps)) cs

introTypeCons :: [Type] -> Type -> TypeCons -> Typing ()
introTypeCons ps t (TypeCons c ts) =
  let ct = case ts of
             [] -> t
             _ -> TFun ts t
      ct' = case ps of
             [] -> MonoType ct
             _ -> PolyType (map (\pt ->
                                   case pt of
                                     TVar tv -> tv
                                     _ -> error $ "Type definition parameter is not a type variable: " ++ (show pt))
                              ps)
                    ct
  in insert c ct'

inferEnv :: [(Ident, (), UExpr)] -> Typing [(Ident, Type, TExpr)]
inferEnv env =
  mapM (\(x, _, ce) -> do
          ce' <- inferExpr ce
          xt <- typeOfName x
          unify xt (typeOf ce')
          return (x, xt, ce'))
    env

inferFunction' :: UFunction -> [Type] -> Type -> Typing TFunction
inferFunction' f prmTys retTy = do
  let prms = map (\((x, _), t) -> (x, MonoType t)) $ zip (fArgs f) prmTys
  e' <- scoped prms $ inferExpr $ fBody f
  unify (typeOf e') retTy
  fty <- realize $ TFun prmTys retTy
  env' <- inferEnv $ fEnv f
  return $ Function { fName = fName f
                    , fType = MonoType fty
                    , fEnv  = env'
                    , fArgs = zip (map fst $ fArgs f) prmTys
                    , fPub  = fPub f
                    , fDeps = fDeps f
                    , fBody = e' }

inferFunction :: UFunction -> Typing TFunction
inferFunction f = do
  prmTys <- mapM (const fresh) $ fArgs f
  retTy <- fresh
  f' <- inferFunction' f prmTys retTy
  case fType f' of
    MonoType fty -> do
      fty' <- generalize fty
      realize $ f' { fType = fty' }
    _ -> error $ "Expected function type to be mono: " ++ (show f)

inferBindings :: [UBinding] -> ([TBinding] -> Typing a) -> Typing a
inferBindings ls innerF =
  let sccs = stronglyConnComp $ map (\l -> (l, bName l, S.toList $ bDeps l)) ls
  in inferWithSccBindings sccs innerF []

inferWithSccBindings :: [SCC UBinding] -> ([TBinding] -> Typing a) -> [TBinding] -> Typing a
inferWithSccBindings [] innerF ls' = innerF $ reverse ls'
inferWithSccBindings ((NECyclicSCC xs):_) _ _ | not $ any (isFun . bBody) xs =
  throwError $ InvalidRecursion $ NE.map bName xs
inferWithSccBindings ((NECyclicSCC xs0:ls)) innerF ls' = do
  let xs = NE.toList xs0
  -- Make fresh variables for everything
  tys <- mapM (\l ->
                 case bBody l of
                   Val _ -> fresh
                   Fun f -> do
                     prmTys <- mapM (const fresh) $ fArgs f
                     retTy <- fresh
                     return $ TFun prmTys retTy
                )
             xs
  -- With the non-generalized variables, infer each item:
  xs' <- scoped (zipWith (\x t -> (bName x, MonoType t)) xs tys) $
          mapM (\(x, t) -> do
                     case bBody x of
                       Val e0 -> do
                         e0' <- inferExpr e0
                         unify (typeOf e0') t
                         return $ x { bType = MonoType t, bBody = Val e0' }
                       Fun f -> do
                         case t of
                           TFun prmTys retTy -> do
                             f' <- inferFunction' f prmTys retTy
                             case fType f' of
                               MonoType fty -> do
                                 unify t fty
                                 return x { bType = MonoType t, bBody = Fun f' }
                               _ -> error $ "Expected montype: " ++ (show f')
                           _ -> error $ "Unexpected type for: " ++ (show t) ++ " for " ++ (show f))
            (zip xs tys)
  -- Then finally generalize and realize the them:
  res <- mapM (\l ->
                 case bBody l of
                   Val e0 -> do
                     t <- realize $ typeOf e0
                     t' <- generalize t
                     return (l { bBody = Val e0 }, t')
                   Fun f -> do
                     case fType f of
                       MonoType fty -> do
                         fty' <- generalize =<< realize fty
                         f' <- realize $ f { fType = fty' }
                         return (l { bBody = Fun f', bType = fType f' }, fType f')
                       _ -> error $ "Expected monotype: " ++ (show f))
           xs'
  -- And do the rest
  scoped (map (\(l, t) -> (bName l, t)) res) $
    inferWithSccBindings ls innerF $ (map fst res) ++ ls'
inferWithSccBindings ((AcyclicSCC l):ls) innerF ls' = do
  (vof, t') <- case bBody l of
      Val e0 -> do
          e0' <- inferExpr e0
          t <- realize $ typeOf e0'
          t' <- generalize t
          return (Val e0', t')
      Fun f  -> do
        f' <- inferFunction f
        return (Fun f', fType f')
  scoped [(bName l, t')] $ inferWithSccBindings ls innerF ((l { bType = t', bBody = vof }):ls')

typeOfName :: Ident -> Typing Type
typeOfName x = lookup x >>= instanciate

litType :: Lit -> Typing Type
litType (LInt _) = return tInt
litType LUnit = return tUnit

inferExpr :: UExpr -> Typing TExpr
inferExpr (ELit _ l) = do
  t <- litType l
  return $ ELit t l
inferExpr (ECapture _ x) = (\t -> ECapture t x) <$> (typeOfName x)
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
  (ls', e') <- inferBindings ls (\ls0 -> ((,) ls0) <$> inferExpr e)
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
inferExpr (ELam _ xs deps caps e0) = do
  prmTys <- mapM (const fresh) xs
  let prms = map fst xs
  let xs' = zipWith (\x t -> (x, MonoType t)) prms prmTys
  caps' <- inferEnv caps
  e0' <- scoped xs' $ inferExpr e0
  return $ ELam (TFun prmTys (typeOf e0')) (zip prms prmTys) deps caps' e0'

inferExpr e = error $ "Type inference is not yet supported for: " ++ (show e)

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

infer :: UModule -> Either TypingError TModule
infer m = runTyping $ do
    mapM_ introTypeConses $ mTypeDefs m
    is <- inferBindings (mItems m) return
    realize $ Module (mName m) (mImports m) (mExports m) (mTypeDefs m) is (mNextId m)
