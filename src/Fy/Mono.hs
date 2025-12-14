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
import Data.List (intersperse, find)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Graph (stronglyConnComp, flattenSCCs)

import Debug.Trace (trace)

data MonoSt = MonoSt { mstKnownTypes :: M.HashMap Ident TypeDef
                     , mstTypeInsts  :: M.HashMap Type TypeDef
                     , mstKnownFuncs :: M.HashMap Ident TFunction
                     , mstFuncInsts  :: M.HashMap (Ident, Type) TFunction }

type Mono = State MonoSt


runMono :: Mono a -> a
runMono m = evalState m $
  MonoSt { mstKnownTypes = M.empty
         , mstTypeInsts  = M.empty
         , mstKnownFuncs = M.empty
         , mstFuncInsts  = M.empty }

registerFun :: TFunction -> Mono ()
registerFun f =
  modify (\s -> s { mstKnownFuncs = M.insert (fName f) f (mstKnownFuncs s) } )

registerFuns :: [TBinding] -> Mono ()
registerFuns bs =
  mapM_ (\x ->
           case x of
             Binding { bBody = Fun f } -> (registerFun f) >> return ()
             _ -> return ())
    bs

instanciate :: Substitutable a => [Type] -> a -> a
instanciate ts x = subst (Subst $ M.fromList $ zip [0 :: Int ..] ts) x

instanciateType :: [Type] -> TypeDef -> Mono TypeDef
instanciateType [] td = return td
instanciateType ts td@(TypeDef tn _ _) = do
  let td' = instanciate ts td
  let instSuffix = T.concat $ "_" : (intersperse "_" $ map encodeType $ map MonoType $ tdParams td')
  monoTypeDef td' { tdName = (tdName td') `suffixId` instSuffix
                  , tdParams = [] }

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
            td' <- instanciateType ts td
            modify (\s -> s { mstTypeInsts = M.insert t td' $ mstTypeInsts s })
            return td'
    Just td -> return td


instanciateFunc :: Ident -> Type -> Mono Ident
instanciateFunc fx ft = do
  mx <- instanciateFunc' fx ft
  case mx of
    Nothing -> error $ "Tried to instanciate unknown function: " ++ (show fx)
    Just x -> return x

tryInstanciateFunc :: Ident -> Type -> Mono Ident
tryInstanciateFunc fx ft@(TFun _ _) = do
  mx <- instanciateFunc' fx ft
  case mx of
    Nothing -> return fx
    Just x -> return x
tryInstanciateFunc fx _ = return fx

instanciateFunc' :: Ident -> Type -> Mono (Maybe Ident)
instanciateFunc' fx ft = do
  when (isNothing $ unFn ft) $ do
    error $ "Non-function type as function head: " ++ (show fx) ++ " : " ++ (show ft)
  st <- get
  case M.lookup (fx, ft) $ mstFuncInsts st of
    Just f -> return $ Just $ fName f
    Nothing -> do
        case M.lookup fx (mstKnownFuncs st) of
          Nothing -> return Nothing
          Just f ->
            case fType f of
              MonoType _ -> return $ Just fx
              PolyType _ rft -> do
                let mF' = runTyping $ do
                            unify rft ft
                            realize $ f { fType = MonoType ft }
                case mF' of
                  Left err -> error $ "Failed to instanciate "
                    ++ (show fx) ++ " as " ++ (show ft)
                    ++ ": " ++ (show err)
                  Right f' -> do
                    let fx' = (fName f') `suffixId` (T.append "_" $ encodeType $ MonoType ft)
                    f'' <- monoFunction $ f' { fName = fx' }
                    modify (\s -> s { mstFuncInsts = M.insert (fx', ft) f'' (mstFuncInsts s) })
                    return $ Just fx'

instanciateFunTy :: [TyVar] -> [Type] -> Type -> Mono TypeDef
instanciateFunTy fvs ts rt = do
  let t = TFun ts rt
  tis <- mstTypeInsts <$> get
  case M.lookup t tis of
    Nothing -> do
      let t' = if null fvs then MonoType t else PolyType fvs t
      let td = TypeDef (mkId $ encodeType t') [] $ TBAlias $ TFun ts rt
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
monoType t@(TFun ts rt) = do
  rt' <- monoType rt
  ts' <- mapM monoType ts
  let fty = TFun ts' rt'
  let fvs = S.toList $ freeVars fty
  ((`TCons` (map TVar fvs)) . tdName) <$> (instanciateFunTy fvs ts' rt')
monoType t@(TCons c ts) = do
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
    Just x -> error $ "Tried to monomorphise the same type twice! " ++ (show td) ++ " vs " ++ (show td')
    Nothing -> do
      modify (\s -> s { mstKnownTypes = M.insert (tdName td') td' $ mstKnownTypes s })
      return td'

monoTypeDef' :: TypeDef -> Mono TypeDef
monoTypeDef' td@(TypeDef _ _ (TBAlias t)) = do
  t' <- monoType t
  return $ td { tdBody = TBAlias t' }
monoTypeDef' td@(TypeDef _ _ (TBConses cs)) = do
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
monoCase (Case p bs e) =
  Case <$> (monoPat p)
       <*> (mapM (\(x, t) -> ((,) x) <$> (monoType t)) bs)
       <*> (monoExpr e)

monoExpr :: TExpr -> Mono TExpr
monoExpr e =
  case e of
    EIdent t x -> error $ "Unexpected EIdent during monomorphisation, expected materialed refs instead: " ++ (show e)
    -- Note that we're trying not to lower the called-function type to an alias here
    EApp t e es -> EApp <$> (monoType t)
                        <*> (monoExpr e)
                        <*> (mapM monoExpr es)
    EIf t e0 e1 e2 -> EIf <$> (monoType t)
                          <*> (monoExpr e0)
                          <*> (monoExpr e1)
                          <*> (monoExpr e2)
    EGlobal t x -> monoName EGlobal t x
    ELocal t x -> monoName ELocal t x
    ECons t cx -> (\t' -> ECons t' cx) <$> (monoType t)
    ETup t es -> ETup <$> (monoType t) <*> (mapM monoExpr es)
    ELet t bs e -> do
      registerFuns bs
      ELet <$> (monoType t)
           <*> (mapM monoBinding bs)
           <*> (monoExpr e)
    ECase t e cs -> ECase <$> (monoType t)
                          <*> (monoExpr e)
                          <*> (mapM monoCase cs)
    _ -> return e
  where
    monoName :: (Type -> Ident -> TExpr) -> Type -> Ident -> Mono TExpr
    monoName c t x = c <$> (monoType t) <*> (tryInstanciateFunc x t)

captureNewDeps :: Mono a -> Mono (a, Set Ident)
captureNewDeps m = do
  oldInsts <- getInstNames
  r <- m
  curInsts <- getInstNames
  let newInsts = curInsts S.\\ oldInsts
  return (r, newInsts)
  where
    getInstNames :: Mono (Set Ident)
    getInstNames = (S.fromList . (map fst) . M.keys . mstFuncInsts) <$> get

-- Handles type schemes, but doesn't alias the toplevel function type
monoSignature :: TypeScheme -> Mono TypeScheme
monoSignature sig =
  case sig of
    MonoType t -> MonoType <$> (monoType' t)
    PolyType xs t -> (PolyType xs) <$> (monoType' t)

monoFunction :: TFunction -> Mono TFunction
monoFunction f = do
  -- The functions that got instantiated while processing the body should
  -- Become dependencies of this function
  (e', newInsts) <- captureNewDeps $ monoExpr $ fBody f
  t' <- monoSignature $ fType f
  args' <- mapM (\(x, t) -> ((,) x) <$> (monoType t)) $ fArgs f
  return $ f { fBody = e'
             , fType = t'
             , fArgs = args'
             , fDeps = S.union (fDeps f) newInsts }

monoBinding :: TBinding -> Mono TBinding
monoBinding b@(Binding { bBody = Val e, bType = t }) = do
  t' <- monoSignature t
  (e', newDeps) <- captureNewDeps $ monoExpr e
  return $ b { bBody = Val e'
             , bDeps = S.union newDeps (bDeps b)
             , bType = t' }
monoBinding b@(Binding { bBody = Fun f }) = do
  f' <- monoFunction f
  return $ b { bBody = Fun f', bDeps = (fDeps f), bType = fType f' }

orderTypeDefs :: [TypeDef] -> [TypeDef]
orderTypeDefs tds =
  let tdGraph = map (\td -> (td, tdName td, S.toList $ typeDeps td)) tds
  in flattenSCCs $ stronglyConnComp tdGraph

orderBindings :: [TBinding] -> [TBinding]
orderBindings bs =
  let bGraph = map (\b -> (b, bName b, S.toList $ bDeps b)) bs
  in flattenSCCs $ stronglyConnComp bGraph

monoModule :: TModule -> Mono TModule
monoModule m = do
  -- First order the known types by dependencies
  let orderedTds = orderTypeDefs $ mTypeDefs m
  tds <- mapM monoTypeDef orderedTds
  registerFuns $ mItems m
  bs' <- mapM monoBinding $ mItems m
  insts <- ((map bindingFromFunction) . M.elems . mstFuncInsts) <$> get
  tds' <- (orderTypeDefs . (tds ++) . M.elems . mstTypeInsts) <$> get
  return $ m { mItems = orderBindings $ insts ++ bs'
             , mTypeDefs = tds' }

monomorphise :: TModule -> TModule
monomorphise m = runMono $ monoModule m
