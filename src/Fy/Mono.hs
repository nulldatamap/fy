module Fy.Mono
  ( monomorphise
  ) where

import Fy.Types
import Fy.Ast
import Fy.Typing hiding (instanciate)

import Control.Monad
import Control.Monad.State
import qualified Data.HashMap.Strict as M
import qualified Data.Text as T
import Data.Maybe (isNothing)
import Data.List (intersperse)
import qualified Data.List.NonEmpty as NE
import Data.Set (Set)
import qualified Data.Set as S
import Data.Graph (stronglyConnComp, flattenSCCs, SCC(..))

data MonoSt = MonoSt { mstKnownTypes :: M.HashMap Ident TypeDef
                     , mstTypeInsts  :: M.HashMap Type TypeDef
                     , mstKnownBindings :: M.HashMap Ident TBinding
                     , mstBindingInsts  :: M.HashMap (Ident, Type) TBinding
                     , mstDeps :: Set Ident }

type Mono = State MonoSt


runMono :: Mono a -> a
runMono m = evalState m $
  MonoSt { mstKnownTypes = M.empty
         , mstTypeInsts  = M.empty
         , mstKnownBindings = M.empty
         , mstBindingInsts  = M.empty
         , mstDeps = S.empty }

registerName :: TBinding -> Mono ()
registerName b =
  modify (\s -> s { mstKnownBindings = M.insert (bName b) b (mstKnownBindings s) } )

registerNames :: [TBinding] -> Mono ()
registerNames bs =
  mapM_ registerName bs

instanciate :: Substitutable a => [Type] -> a -> a
instanciate ts x = subst (Subst $ M.fromList $ zip [0 :: Int ..] ts) x

instanciateType :: Type -> [Type] -> TypeDef -> Mono TypeDef
instanciateType _ [] td = return td
instanciateType t ts td = do
  let td' = instanciate ts td
  let instSuffix = T.concat $ "_" : (intersperse "_" $ map encodeType $ map MonoType $ tdParams td')
  let td'' = td' { tdName = (tdName td') `suffixId` instSuffix
                 , tdParams = [] }
  modify (\s -> s { mstTypeInsts = M.insert t td'' $ mstTypeInsts s })
  monoTypeDef td''

instanciateTypeDef :: Ident -> [Type] -> Mono TypeDef
instanciateTypeDef c ts = do
  let t = TCons c ts
  tis <- mstTypeInsts <$> get
  case M.lookup t tis of
    Nothing -> do
        tds <- mstKnownTypes <$> get
        case M.lookup c tds of
          Nothing -> error $ "Couldn't resolve type: " ++ (show t)
          Just td -> do
            td' <- instanciateType t ts td
            modify (\s -> s { mstTypeInsts = M.insert t td' $ mstTypeInsts s })
            return td'
    Just td -> return td


tryInstanciateBinding :: Ident -> Type -> Mono Ident
tryInstanciateBinding x t | not $ null $ freeVars t = return x
tryInstanciateBinding x t@(TFun _ _) = do
  mx <- instanciateBinding' x t
  case mx of
    Nothing -> return x
    Just x' -> return x'
tryInstanciateBinding x _ = return x

instanciateBinding' :: Ident -> Type -> Mono (Maybe Ident)
instanciateBinding' x t = do
  when (isNothing $ unFn t) $ do
    error $ "Non-function type as function head: " ++ (show x) ++ " : " ++ (show t)
  st <- get
  case M.lookup (x, t) $ mstBindingInsts st of
    Just b -> return $ Just $ bName b
    Nothing -> do
        case M.lookup x (mstKnownBindings st) of
          Nothing -> return Nothing
          Just b ->
            case bType b of
              MonoType _ -> return $ Just x
              PolyType _ rt -> do
                let mB' = runTyping $ do
                            unify rt t
                            t' <- generalize =<< realize t
                            realize $ b { bType = t' }
                case mB' of
                  Left err -> error $ "Failed to instanciate "
                    ++ (show x) ++ " as " ++ (show t)
                    ++ ": " ++ (show err)
                  Right b' -> do
                    let x' = (bName b') `suffixId` (T.append "_" $ encodeType $ bType b')
                    modify (\s -> s { mstBindingInsts = M.insert (x, t) b' { bName = x' } (mstBindingInsts s) })
                    b'' <- monoBinding $ b' { bName = x' }
                    modify (\s -> s { mstBindingInsts = M.insert (x, t) b'' (mstBindingInsts s) })
                    return $ Just x'

instanciateFunTy :: [TyVar] -> [Type] -> Type -> Mono TypeDef
instanciateFunTy fvs ts rt = do
  let t = TFun ts rt
  tis <- mstTypeInsts <$> get
  case M.lookup t tis of
    Nothing -> do
      let t' = if null fvs then MonoType t else PolyType fvs t
      let td = TypeDef (mkId $ encodeType t') [] S.empty $ TBAlias $ TFun ts rt
      modify (\s -> s { mstTypeInsts = M.insert t td $ mstTypeInsts s })
      return td
    Just td -> return td

monoType' :: Type -> Mono Type
monoType' (TFun ts rt) = TFun <$> (mapM monoType ts) <*> (monoType rt)
monoType' t = monoType t

monoType :: Type -> Mono Type
monoType t | isBuiltinType t = return t
monoType t@(TVar _) = return t
monoType t@(TCons _ []) = return t
monoType (TFun ts rt) = do
  rt' <- monoType rt
  ts' <- mapM monoType ts
  let fty = TFun ts' rt'
  return fty
monoType (TCons c ts) = do
  ts' <- mapM monoType ts
  if null $ foldMap freeVars ts'
  then ((`TCons` []) . tdName) <$> instanciateTypeDef c ts'
  else return $ TCons c ts'

monoTypeDef :: TypeDef -> Mono TypeDef
monoTypeDef td = do
  -- Just a safety check
  ktds <- mstKnownTypes <$> get
  td' <- monoTypeDef' td
  case M.lookup (tdName td') ktds of
    Just _ -> error $ "Tried to monomorphise the same type twice! " ++ (show td) ++ " vs " ++ (show td')
    Nothing -> do
      modify (\s -> s { mstKnownTypes = M.insert (tdName td') td' $ mstKnownTypes s })
      return td'

monoTypeDef' :: TypeDef -> Mono TypeDef
monoTypeDef' td@(TypeDef _ _ _ (TBAlias t)) = do
  t' <- monoType t
  return $ td { tdBody = TBAlias t' }
monoTypeDef' td@(TypeDef _ _ _ (TBConses cs)) = do
  cs' <- mapM monoTypeCons cs
  return $ td { tdBody = TBConses cs' }
  where
    monoTypeCons :: TypeCons -> Mono TypeCons
    monoTypeCons (TypeCons n ms) = (TypeCons n) <$> (mapM monoType ms)
monoTypeDef' td = return td

monoPat :: TPat -> Mono TPat
monoPat (PHole t) = PHole <$> (monoType t)
monoPat (PBinding t x) = (`PBinding` x) <$> (monoType t)
monoPat (PCons t c ps) = PCons <$> (monoType t) <*> (return c) <*> (mapM monoPat ps)
monoPat p = return p

monoCase :: TCase -> Mono TCase
monoCase (Case p bs e) = do
  p' <- monoPat p
  bs' <- mapM (\(x, t) -> ((,) x) <$> (monoType t)) bs
  e' <- monoExpr e
  modify (\s -> s { mstDeps = (mstDeps s) S.\\ (S.fromList $ map fst bs) })
  return $ Case p' bs' e'

monoExpr :: TExpr -> Mono TExpr
monoExpr e =
  case e of
    EIdent _ _ -> error $ "Unexpected EIdent during monomorphisation, expected materialed refs instead: " ++ (show e)
    -- Note that we're trying not to lower the called-function type to an alias here
    EApp t e0 es -> EApp <$> (monoType t)
                         <*> (monoExpr e0)
                         <*> (mapM monoExpr es)
    EIf t e0 e1 e2 -> EIf <$> (monoType t)
                          <*> (monoExpr e0)
                          <*> (monoExpr e1)
                          <*> (monoExpr e2)
    EGlobal t x -> monoName EGlobal t x
    ELocal t x -> monoName ELocal t x
    ECons t cx -> (\t' -> ECons t' cx) <$> (monoType t)
    ETup t es -> ETup <$> (monoType t) <*> (mapM monoExpr es)
    ELet t bs e0 -> do
      registerNames bs
      ELet <$> (monoType t)
           <*> (mapM monoBinding bs)
           <*> (monoExpr e0)
    ECase t e0 cs -> ECase <$> (monoType t)
                           <*> (monoExpr e0)
                           <*> (mapM monoCase cs)
    ELam t xs deps caps e0 ->
      ELam <$> (monoType t)
           <*> (mapM (\(x, t0) -> ((,) x) <$> (monoType t0)) xs)
           <*> (return deps)
           <*> (mapM (\(cx, ct, ce) -> ((,,) cx) <$> (monoType ct) <*> (monoExpr ce)) caps)
           <*> (monoExpr e0)
    _ -> return e
  where
    monoName :: (Type -> Ident -> TExpr) -> Type -> Ident -> Mono TExpr
    monoName c t x = do
      t' <- monoType' t
      x' <- tryInstanciateBinding x t
      modify (\s -> s { mstDeps = S.insert x' $ mstDeps s })
      return $ c t' x'

-- Handles type schemes, but doesn't alias the toplevel function type
monoSignature :: TypeScheme -> Mono TypeScheme
monoSignature sig =
  case sig of
    MonoType t -> MonoType <$> (monoType' t)
    PolyType xs t -> (PolyType xs) <$> (monoType' t)

captureNewDeps :: Mono a -> Mono (a, Set Ident)
captureNewDeps m = do
  oldDeps <- mstDeps <$> get
  modify (\s -> s { mstDeps = S.empty })
  r <- m
  newDeps <- mstDeps <$> get
  modify (\s -> s { mstDeps = oldDeps })
  return (r, newDeps)

monoFunction :: TFunction -> Mono TFunction
monoFunction f = do
  t' <- monoSignature $ fType f
  (e', newDeps) <- captureNewDeps $ monoExpr $ fBody f
  args' <- mapM (\(x, t) -> ((,) x) <$> (monoType t)) $ fArgs f
  env' <- mapM (\(cx, ct, ce) -> ((,,) cx) <$> (monoType ct) <*> (monoExpr ce)) $ fEnv f
  return $ f { fBody = e'
             , fType = t'
             , fEnv = env'
             , fArgs = args'
             , fDeps = newDeps S.\\ (S.fromList $ map fst $ fArgs f) }

monoBinding :: TBinding -> Mono TBinding
monoBinding b@(Binding { bBody = Val e, bType = t }) = do
  t' <- monoSignature t
  (e', newDeps) <- captureNewDeps $ monoExpr e
  return $ b { bBody = Val e'
             , bDeps = newDeps
             , bType = t' }
monoBinding b@(Binding { bBody = Fun f }) = do
  -- The binding might have been renamed and we'll propagate that here
  f' <- monoFunction $ f { fName = bName b, fType = bType b }
  return $ b { bBody = Fun f', bDeps = (fDeps f), bType = fType f' }

orderTypeDefs :: [TypeDef] -> [TypeDef]
orderTypeDefs tds =
  let tdGraph = map (\td -> (td, tdName td, S.toList $ typeDeps td)) tds
  in annotateRecGroups $ stronglyConnComp tdGraph
  where
    annotateRecGroups [] = []
    annotateRecGroups ((NECyclicSCC xs0):sccs) =
      let xs = NE.toList xs0
      in map (\td -> td { tdRecursionGroup = (S.fromList $ map tdName xs) }) xs
           ++ (annotateRecGroups sccs)
    annotateRecGroups ((AcyclicSCC x):sccs) = x:(annotateRecGroups sccs)

orderBindings :: [TBinding] -> [TBinding]
orderBindings bs =
  let bGraph = map (\b -> (b, bName b, S.toList $ bDeps b)) bs
  in flattenSCCs $ stronglyConnComp bGraph

monoModule :: TModule -> Mono TModule
monoModule m = do
  -- First order the known types by dependencies
  let orderedTds = orderTypeDefs $ mTypeDefs m
  tds <- mapM monoTypeDef orderedTds
  registerNames $ mItems m
  bs' <- mapM monoBinding $ mItems m
  insts <- (M.elems . mstBindingInsts) <$> get
  tds' <- (orderTypeDefs . (tds ++) . M.elems . mstTypeInsts) <$> get
  return $ m { mItems = orderBindings $ insts ++ bs'
             , mTypeDefs = tds' }

monomorphise :: TModule -> TModule
monomorphise m = runMono $ monoModule m
