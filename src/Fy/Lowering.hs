module Fy.Lowering
  ( lowerToIR
  ) where

import Fy.Util
import Fy.Pretty
import Fy.Types
import Fy.Ast
import Fy.Ir

import Prelude hiding (lookup, lines)
import Data.Text (Text)
import Data.Set (Set)
import qualified Data.Set as S
import Data.List (find)
import Data.Maybe
import Data.Tuple.Extra (first)
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.RWS.Strict
import qualified Data.HashMap.Strict as M

import Debug.Trace (trace)

data NameKind = NKBareFunc
              | NKCloFunc IRType
              | NKVal
              deriving (Show)

data LoweringSt = LoweringSt { lstNext  :: Int
                             , lstFuncs :: [IRFunc]
                             , lstNames :: M.HashMap Ident (IRType, NameKind)
                             , lstTypes :: M.HashMap Ident IRTypeDef
                             , lstExtraTypes :: [IRTypeDef] }

type Lowering = RWS () [IRStmt] LoweringSt

data IRTypeKind = IRTDef IRTypeDef
                | IRTBox
                | IRTClo IRFPtrType
                | IRTBuiltin Ident
                deriving (Show)

runLowering :: Lowering a -> a
runLowering m = fst $ evalRWS m () $
  LoweringSt { lstNext  = 0
             , lstFuncs = []
             , lstTypes = M.empty
             , lstNames = M.empty
             , lstExtraTypes = []
             }

newVar' :: (Maybe Text) -> Lowering Ident
newVar' t = do
  x <- lstNext <$> get
  modify (\s -> s { lstNext = x + 1 } )
  return $ Ident (fromMaybe "__" t) [] (Just x)

declareName :: Ident -> IRType -> NameKind -> Lowering ()
declareName n t nk = do
  modify (\s -> s { lstNames = M.insert n (t, nk) $ lstNames s })

nameKind :: Ident -> Lowering NameKind
nameKind n = do
  nks <- lstNames <$> get
  case M.lookup n nks of
    -- We don't register parameters and case bindings, since they're always values
    Nothing -> return NKVal
    Just (_, nk) -> return nk

nameType :: Ident -> Lowering IRType
nameType n = do
  nks <- lstNames <$> get
  case M.lookup n nks of
    Nothing -> error $ "Unresolved name: " ++ (show n)
    Just (t, _) -> return t

irSet :: IRType -> Ident -> (IRExpr, IRType) -> Lowering ()
irSet xt x (v, vt) = do
  v' <- matchBoxing xt vt v
  tell [ IRSet x v' ]

irDef' :: IRType -> Ident -> (Maybe (IRExpr, IRType)) -> Lowering [IRStmt]
irDef' xt x Nothing = return [ IRDef xt x Nothing ]
irDef' xt x (Just (v, vt)) = do
  v' <- matchBoxing xt vt v
  return [ IRDef xt x (Just v') ]

irDef :: IRType -> Ident -> (Maybe (IRExpr, IRType)) -> Lowering ()
irDef xt x v = do
  d <- irDef' xt x v
  tell d

lowerBinding :: TBinding -> Lowering ()
lowerBinding (Binding t x _ _ (Val e)) = do
  t0' <- case t of
           MonoType t0 -> lowerType t0
           PolyType _ t0 -> lowerType t0
  declareName x t0' NKVal
  te' <- lowerExpr e
  irDef t0' x (Just te')
lowerBinding b = error $ "Function found in local binding: " ++ (show b)

stmts :: Lowering a -> Lowering (a, [IRStmt])
stmts m = censor (const []) $ listen m

lowerLit :: Lit -> (IRLit, IRType)
lowerLit (LInt i) = (IRInt i, irtInt)
lowerLit LUnit = (IRVoid, irtUnit)

resolveType :: IRType -> Lowering IRTypeKind
resolveType (IRType tn) | tn `elem` builtinTypeNames = return $ IRTBuiltin tn
resolveType IRBoxType = return $ IRTBox
resolveType (IRCloType fptr) = return $ IRTClo fptr
resolveType (IRType tn) = do
  tys <- lstTypes <$> get
  case M.lookup tn tys of
    Nothing -> error $ "Unresolved type during lowering: " ++ (show tn)
    Just td ->
      case td of
        IRTypeDef { irtdBody = IRTypeAlias tn' } -> resolveType tn'
        _ -> return $ IRTDef td

isBoxType :: IRType -> Lowering Bool
isBoxType t = do
  t' <- resolveType t
  return $
    case t' of
      IRTBox -> True
      IRTBuiltin _ -> False
      -- Closures are not boxed! They're an unboxed function-pointer - environment-pointer pair
      IRTClo _ -> False
      IRTDef td -> irtdIsBoxed td

irField :: (Maybe IRTypeDef) -> IRExpr -> Ident -> IRExpr
irField mTd obj fld =
  if fromMaybe False $ irtdIsBoxed <$> mTd
  then IRField (IRUnbox Nothing obj) fld
  else IRField obj fld

irCheckVariant :: IRTypeDef -> IRExpr -> Ident -> IRExpr
irCheckVariant td obj var =
  if irtdIsBoxed td
  then IRCheckVariant (IRUnbox Nothing obj) var
  else IRCheckVariant obj var

boxExpr :: IRType -> IRType -> IRExpr -> Lowering IRExpr
boxExpr tt it e = do
  x <- newVar' (Just "_box")
  tell [ IRBox tt x it e ]
  return $ IRVar x

matchBoxing :: IRType -> IRType -> IRExpr -> Lowering IRExpr
matchBoxing targetTy incomingTy e = do
  tb <- isBoxType targetTy
  ib <- isBoxType incomingTy
  case (tb, ib) of
    (True, False) -> boxExpr targetTy incomingTy e
    (False, True) -> return $ IRUnbox (Just targetTy) e
    _ -> return e

boxArguments :: [IRType] -> [(IRExpr, IRType)] -> Lowering [IRExpr]
boxArguments ts args =
  mapM (\(targetT, (e, incomingT)) ->
          matchBoxing targetT incomingT e)
    (zip ts args)

spillExpr :: Text -> TExpr -> Lowering Ident
spillExpr n e = do
  (e', t') <- lowerExpr e
  case e' of
    IRVar x -> return x
    _ -> do
      x <- newVar' (Just n)
      tell [ IRDef t' x $ Just e' ]
      return x

irCons :: IRType -> Ident -> [IRExpr] -> Lowering (IRExpr, IRType)
irCons t c xs = do
  t' <- resolveType t
  case t' of
    IRTDef td -> do
      let ce = IRCons t c xs
      if irtdIsBoxed td
      then do
        ce' <- boxExpr t t ce
        return (ce', t)
      else return (ce, t)
    _ -> error $ "Non data-structure type for constructor! type: "
                   ++ (show t) ++ " (" ++ (show t') ++ ") " ++ " cons: " ++ (show c)

-- irTypeOf :: TExpr -> IRExpr -> Lowering IRType
-- irTypeOf e e' = do
--   mT <- case e' of
--           IRVar x -> nameType x
--           IRClosure f _ -> nameType f
--           IRCall f _ -> do
--             mT <- nameType f
--             case mT of
--               Nothing -> return Nothing
--               Just t -> do
--                 (IRFPtrType rt _) <- resolveToFPtrType t
--                 return $ Just rt
--           _ -> return Nothing
--   t' <- lowerType (typeOf e)
--   return $ fromMaybe t' mT

lowerFunType :: Type -> Lowering (IRType, [IRType])
lowerFunType (TFun ts t) = (,) <$> (lowerType t) <*> (mapM lowerType ts)
lowerFunType (TCons t _) = do
  td <- lookupTypeDef t
  case irtdBody td of
    IRFunType (IRFPtrType ts rt) -> return (ts, rt)
    _ -> error $ "Expected a function type: " ++ (show t)
lowerFunType t = error $ "Expected function type: " ++ (show t)

lowerClosure :: (Maybe IRType) -> Ident -> [TExpr] -> Lowering (IRExpr, IRType)
lowerClosure t f es = do
  t' <- nameType f
  e <- sequence $
              (\t0 -> do
                 es' <- (map fst) <$> (mapM lowerExpr es)
                 fst <$> (irCons t0 (mkId "") es')) <$> t
  return $ (IRClosure f e, t')

lowerExpr :: TExpr -> Lowering (IRExpr, IRType)
lowerExpr e = do
  (e', t) <- lowerExpr0 e
  case e' of
    IRVar x -> do
      nk <- nameKind x
      case nk of
        NKVal -> return (e', t)
        NKCloFunc _ -> error $ "Bare function name referenced, but it's a closure function: " ++ (show e)
        NKBareFunc -> lowerClosure Nothing x []
    _ -> return (e', t)

resolveToFPtrType :: IRType -> Lowering IRFPtrType
resolveToFPtrType t =
  case t of
    IRType x -> do
      td <- lookupTypeDef x
      case irtdBody td of
        IRTypeAlias x' -> resolveToFPtrType x'
        IRFunType fptr -> return fptr
        _ -> error $ "Expected function type, got: " ++ (show td)
    IRCloType fptr -> return fptr
    IRBoxType -> error $ "Expected function type, got: " ++ (show t)

lowerExpr0 e = do
  (e', t) <- lowerExpr0' e
  return $ trace ((show $ cpretty e) ++ " : " ++ (show $ cpretty t))(e', t)
-- TODO: Default lowerExpr should also infer the type
-- Doesn't do closure lifting
lowerExpr0' :: TExpr -> Lowering (IRExpr, IRType)
lowerExpr0' e =
  case e of
    ELit _ l -> return $ first IRLit $ lowerLit l
    EBuiltin _ _ -> error $ "Bare operatior: " ++ (show e)
    ECons t (Ident cn _ _) -> do
      t' <- lowerType t
      irCons t' (mkId cn) []
    ELocal _ x -> lowerName IRVar x
    EGlobal _ x -> lowerName IRVar x
    ECapture _ x -> lowerName IREnv x
    EIdent _ _ -> error $ "EIdent found during lowering: " ++ (show e)
    EApp t (EBuiltin _ b) xs -> do
      t' <- lowerType t
      xs' <- (map fst) <$> mapM lowerExpr xs
      let o = case b of
                BAdd -> OpAdd
                BEq  -> OpEq
      return $ (IROp o xs', t')
    EApp t fe xs -> do
      case fe of
        ECons _ c@(Ident cn _ _) -> do
          ft' <- nameType c
          (IRFPtrType retTy prmTys) <- resolveToFPtrType ft'
          xs' <- (boxArguments prmTys) =<< (mapM lowerExpr xs)
          irCons retTy (mkId cn) xs'
        _ -> do
          (fe', ft') <- lowerExpr0 fe
          (IRFPtrType retTy prmTys) <- resolveToFPtrType ft'
          xs' <- (boxArguments prmTys) =<< (mapM lowerExpr xs)
          fty <- (uncurry IRFPtrType) <$> (lowerFunType (typeOf fe))
          c <- case fe' of
                 IRVar fx -> do
                   nk <- nameKind fx
                   case nk of
                     NKVal -> return $ IRInvoke fty fe'
                     NKCloFunc _ ->
                       error $ "Bare function name referenced, but it's a closure function: " ++ (show fe)
                     NKBareFunc -> return $ IRCall fx
                 _ -> do
                   fptr <- newVar' (Just "_clov")
                   irDef (IRCloType fty) fptr (Just (fe', IRCloType fty))
                   return $ IRInvoke fty (IRVar fptr)
          return $ (c xs', retTy)
    ELet _ ls e0 -> do
      mapM_ lowerBinding ls
      lowerExpr e0
    EIf t e0 e1 e2 -> do
      r <- newVar' (Just "_phi")
      t' <- lowerType t
      irDef t' r Nothing
      (e0', _) <- lowerExpr e0
      (_, sts1) <- stmts $ do
        te1' <- lowerExpr e1
        irSet t' r te1'
      (_, sts2) <- stmts $ do
        te2' <- lowerExpr e2
        irSet t' r te2'
      tell [ IRIf e0' sts1 sts2 ]
      return $ (IRVar r, t')
    ECase t e0 cs -> do
      x <- spillExpr "_matchee" e0
      lowerCases x t cs
    EClo _ f es -> do
      nk <- nameKind f
      case nk of
        NKCloFunc ct -> lowerClosure (Just ct) f es
        NKBareFunc -> lowerClosure Nothing f []
        _ -> error $ "Closure " ++ (show e) ++ " doesn't refer to a closure function: " ++ (show nk)
    _ -> error $ "Lowering is not yet supported for: " ++ (show e)
  where
    lowerName :: (Ident -> IRExpr) -> Ident -> Lowering (IRExpr, IRType)
    lowerName c x = do
      t <- nameType x
      return (c x, t)

lookupTypeDef :: Ident -> Lowering IRTypeDef
lookupTypeDef t = do
  tis <- lstTypes <$> get
  case M.lookup t tis of
    Nothing -> error $ "Unresolved type during lowering: " ++ (show t)
    Just td -> return td

lowerType' :: Set Ident -> Type -> Lowering IRType
lowerType' rg (TCons x _) | S.member x rg = return $ IRType x
lowerType' _ t = lowerType t

lowerType :: Type -> Lowering IRType
lowerType (TBox _) = return IRBoxType
lowerType t@(TVar _) = error $ "Unexpected bare type variable: " ++ (show t)
lowerType t@(TCons x []) | isBuiltinType t = return $ IRType x
lowerType (TCons t _) = do
  td <- lookupTypeDef t
  return $ IRType $ irtdName td
lowerType (TFun ts t) =
  IRCloType <$> (IRFPtrType <$> (lowerType t) <*> (mapM lowerType ts))

lowerPattern :: TPat -> IRExpr -> [IRStmt] -> Lowering ([IRExpr], [IRStmt])
lowerPattern (PHole _) _ bs = return ([], bs)
lowerPattern (PLit _ l) path bs = return ([IROp OpEq [path, (IRLit . fst) $ lowerLit l]], bs)
lowerPattern (PBinding t x) path bs = do
  t' <- lowerType t
  return ([], bs ++ [IRDef t' x $ Just path])
lowerPattern (PCons (TCons t _) c ps) path bs = do
  td <- lookupTypeDef t
  let tn = irtdName td
  case irtdBody td of
    IRFunType _ -> error $ "Tried to match a function pointer type with a constructor? "
                         ++ (show c) ++ " : " ++ (show t)
    IRCType _ -> error $ "Tried to match a ctype with a constructor? " ++ (show c) ++ " : " ++ (show t)
    IREnumType _ -> do
      (irc, _) <- irCons (IRType tn) c []
      return ([IROp OpEq [path, irc]], bs)
    IRStructType (IRRecord _ fs) -> lowerRecordPattern (Just td) ps bs path fs
    IRTaggedType rs -> do
      case find (\(IRRecord c0 _) -> (bare c) == c0) rs of
        Nothing -> error $ "Couldn't find constructor `" ++ (show c) ++ "` in type: " ++ (show t)
        Just (IRRecord _ fs) -> do
          (cs, bs') <- lowerRecordPattern Nothing ps bs (irField (Just td) path (bare c)) fs
          return ((irCheckVariant td path (tn <> (bare c))):cs, bs')
    IRTypeAlias (IRType t') ->
      lowerPattern (PCons (TCons t' []) c ps) path bs
    _ -> error $ "Invalid pattern cons type: " ++ (show td)
lowerPattern (PCons c _ _) _ _ = error $ "Invalid pattern cons type: " ++ (show c)

lowerRecordPattern :: (Maybe IRTypeDef) -> [TPat] -> [IRStmt] -> IRExpr -> [(IRType, Ident)]
                   -> Lowering ([IRExpr], [IRStmt])
lowerRecordPattern mTd ps bs0 path fs =
    foldM (\(cs, bs) ((_, f), p) -> do
            (cs', bs') <- lowerPattern p (irField mTd path f) bs
            return (cs ++ cs', bs'))
    ([], bs0)
    (zip fs ps)

lowerCases :: Ident -> Type -> [TCase] -> Lowering (IRExpr, IRType)
lowerCases matchVar rTy cases = do
  r <- newVar' (Just "_phi")
  rTy' <- lowerType rTy
  irDef rTy' r Nothing
  makeIfElseChain =<< mapM (lowerCase rTy' r) cases
  return $ (IRVar r, rTy')
  where
    lowerCase rTy' r (Case p _ e) = do
      (eCs, bs) <- lowerPattern p (IRVar matchVar) []
      (_, sts) <- stmts $ do
         te' <- lowerExpr e
         irSet rTy' r te'
      return (eCs, bs ++ sts)
    makeIfElseChain [([], body)] = tell body
    makeIfElseChain [] = tell [ IRPanic "Uncovered match case" ]
    makeIfElseChain ((eCs, body):xs) = do
      (_, sts2) <- stmts $ makeIfElseChain xs
      tell [ IRIf (IROp OpAnd eCs) body sts2 ]

lowerBody :: IRType -> TExpr -> Lowering ()
lowerBody tt b = do
  (r, it) <- lowerExpr b
  r' <- matchBoxing tt it r
  tell [ IRReturn r' ]

lowerEnvType :: Ident -> [(Ident, Type, TExpr)] -> Lowering IRType
lowerEnvType fn env = do
  let tn = fn `suffixId` "_env"
  flds <- mapM (\(x, t, _) -> do
                   t' <- lowerType t
                   return (t', x))
            env
  let td = IRTypeDef tn S.empty True $ IRStructType $ IRRecord (mkId "") flds
  modify (\s -> s { lstTypes = M.insert tn td $ lstTypes s
                  , lstExtraTypes = td : (lstExtraTypes s) })
  return $ IRType tn

declareFunction :: TFunction -> Lowering (IRType, [IRType], Maybe IRType)
declareFunction f = do
  let fn = fName f
  let fty = case fType f of
              MonoType mt -> mt
              PolyType _ pt -> pt
  let (_, retT) = case unFn fty of
                Nothing -> error "Type of function isn't a arrow type!"
                Just x -> x
  argTs <- mapM (lowerType . snd) $ fArgs f
  retT' <- lowerType retT
  let t = (IRCloType $ IRFPtrType retT' argTs)
  if null $ fEnv f
  then do
    declareName fn t NKBareFunc
    return (retT', argTs, Nothing)
  else do
    et <- lowerEnvType fn $ fEnv f
    declareName fn t $ NKCloFunc et
    return (retT', argTs, Just et)

lowerFunction :: TFunction -> IRType -> [IRType] -> (Maybe IRType) -> Lowering IRFunc
lowerFunction f retTy argTs envTy = do
  let argTs' = zipWith (\(x, _) t -> (x, t)) (fArgs f) argTs
  mapM_ (\(x, t) -> declareName x t NKVal) argTs'
  (_, body) <- stmts $ lowerBody retTy $ fBody f
  let f' = IRFunc { irfName  = fName f
                  , irfPub   = fPub f
                  , irfRetTy = retTy
                  , irfArgs  = argTs'
                  , irfEnv   = envTy
                  , irfDeps  = fDeps f
                  , irfBody  = body }
  modify (\s -> s { lstFuncs = f' : (lstFuncs s) })
  return f'

lowerVals :: [TBinding] -> Lowering ([IRVarDecl], [IRStmt])
lowerVals bs = stmts $
  mapM (\b ->
          case b of
           (Binding t x p _ (Val e)) -> do
             let t0 = case t of
                        MonoType mt -> mt
                        PolyType _ pt -> pt
             te' <- lowerExpr e
             t0' <- lowerType t0
             irSet t0' x te'
             return $ IRVarDecl x p t0'
           _ -> error $ "Function binding passed to lowerVals: " ++ (show b))
    bs

mkTypeDef :: Ident -> Set Ident -> IRTypeBody -> IRTypeDef
mkTypeDef n rg b = IRTypeDef n rg False b

lowerTypeDef :: TypeDef -> Lowering IRTypeDef
lowerTypeDef td = do
  td' <- lowerTypeDef' td
  return $ annotateType td'

lowerTypeDef' :: TypeDef -> Lowering IRTypeDef
lowerTypeDef' (TypeDef n _ _ (TBCType ct)) = return $ mkTypeDef n S.empty $ IRCType ct
lowerTypeDef' (TypeDef _ _ _ (TBConses [])) = error $ "Zero types are not supported yet"
lowerTypeDef' (TypeDef n _ rg (TBConses [(TypeCons c ts)])) = do
  ts' <- mapM (lowerType' rg) ts
  declareName c (IRCloType (IRFPtrType (IRType n) ts')) NKBareFunc
  let r = IRRecord (bare c) $ zip ts' unnamedFields
  return $ mkTypeDef n rg $ IRStructType r
lowerTypeDef' (TypeDef n _ rg (TBConses cs)) = do
  if allTags
  then do
    mapM_ (\v -> declareName v (IRType n) NKVal) variants
    return $ mkTypeDef n rg $ IREnumType $ reverse variants
  else do
    rs <- mapM (\(TypeCons c ts) -> do
                    ts' <- mapM (lowerType' rg) ts
                    declareName c (IRCloType (IRFPtrType (IRType n) ts')) NKBareFunc
                    return $ IRRecord (bare c) $ zip ts' unnamedFields)
           cs
    return $ mkTypeDef n rg $ IRTaggedType rs
  where
    (allTags, variants) =
      foldl (\(a, vs) (TypeCons v ts) -> (a && (null ts), (bare v) : vs)) (True, []) cs
lowerTypeDef' (TypeDef n _ rg (TBAlias (TFun ts t))) = do
  ts' <- mapM (lowerType' rg) ts
  t' <- lowerType' rg t
  return $ mkTypeDef n rg $ IRFunType (IRFPtrType t' ts')
lowerTypeDef' (TypeDef n _ rg (TBAlias t)) = do
  t' <- lowerType' rg t
  return $ mkTypeDef n rg $ IRTypeAlias t'

annotateType :: IRTypeDef -> IRTypeDef
annotateType td@(IRTypeDef _ recGroup _ body) =
  td { irtdIsBoxed = isBoxed }
  where
    isBoxed =
      if S.null recGroup
      then
        case body of
          -- TODO: Add a heuristic for when not to box structs and tagged types
          IRStructType (IRRecord _ [_]) -> False
          IRStructType _ -> True
          IRTaggedType _ -> True
          _ -> False
      else True

lowerTypeDefs :: [TypeDef] -> Lowering [IRTypeDef]
lowerTypeDefs tds = do
  mapM (\td -> do
          td' <- lowerTypeDef td
          modify (\s -> s { lstTypes = M.insert (irtdName td') td' (lstTypes s) })
          return td')
    tds

lowerModule :: TModule -> Lowering IRProgram
lowerModule m = do
  tds' <- lowerTypeDefs $ mTypeDefs m
  let (vals, funs) = partitionWith (\b ->
                                      case b of
                                        Binding { bBody = (Fun f) } -> Right f
                                        _ -> Left b)
                         (mItems m)
  fTs <- mapM declareFunction funs
  mapM_ (\(f, (retTy, argTs, envTy)) -> lowerFunction f retTy argTs envTy) $ zip funs fTs
  (vs, inits) <- lowerVals vals
  fs <- lstFuncs <$> get
  ets <- lstExtraTypes <$> get
  return $ IRProgram { irpName  = mName m
                     , irpTypes = tds' ++ ets
                     , irpFuncs = reverse fs
                     , irpVars  = vs
                     , irpInit  = inits }

lowerToIR :: TModule -> IRProgram
lowerToIR m = runLowering $ lowerModule m
