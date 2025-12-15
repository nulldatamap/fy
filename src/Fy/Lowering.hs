module Fy.Lowering
  ( lowerToIR
  ) where


import Fy.Util
import Fy.Types
import Fy.Ast
import Fy.Ir

import Prelude hiding (lookup, lines)
import Data.Text (Text)
import Data.Set (Set)
import qualified Data.Set as S
import Data.List (find)
import Data.Maybe
import Control.Monad
import Control.Monad.State
import Control.Monad.RWS
import qualified Data.HashMap.Strict as M

import Debug.Trace (trace)

data LoweringSt = LoweringSt { lstNext  :: Int
                             , lstFuncs :: [IRFunc]
                             , lstTypes :: M.HashMap Ident IRTypeDef }

type Lowering = RWS () [IRStmt] LoweringSt

data IRTypeKind = IRTDef IRTypeDef
                | IRTBox
                | IRTBuiltin Ident
                deriving (Show)

runLowering :: Lowering a -> a
runLowering m = fst $ evalRWS m () $
  LoweringSt { lstNext  = 0
             , lstFuncs = []
             , lstTypes = M.empty
             }

newVar' :: (Maybe Text) -> Lowering Ident
newVar' t = do
  x <- lstNext <$> get
  modify (\s -> s { lstNext = x + 1 } )
  return $ Ident (fromMaybe "__" t) [] (Just x)

irSet :: IRType -> Ident -> (IRType, IRExpr) -> Lowering ()
irSet xt x (vt, v) = do
  v' <- matchBoxing xt vt v
  tell [ IRSet x v' ]

irDef' :: IRType -> Ident -> (Maybe (IRType, IRExpr)) -> Lowering [IRStmt]
irDef' xt x Nothing = return [ IRDef xt x Nothing ]
irDef' xt x (Just (vt, v)) = do
  v' <- matchBoxing xt vt v
  return [ IRDef xt x (Just v') ]

irDef :: IRType -> Ident -> (Maybe (IRType, IRExpr)) -> Lowering ()
irDef xt x v = do
  d <- irDef' xt x v
  tell d

lowerBinding :: TBinding -> Lowering ()
lowerBinding l@(Binding t x _ _ (Val e)) = do
  te' <- lowerExpr' e
  case t of
    MonoType t0 -> do
      t0' <- lowerType t0
      irDef t0' x (Just te')
    _ -> error $ "Can't lower a polytype local: " ++ (show l)
lowerBinding (Binding { bBody = Fun f }) = lowerFunction f >> return ()

stmts :: Lowering a -> Lowering (a, [IRStmt])
stmts m = censor (const []) $ listen m

lowerLit :: Lit -> IRLit
lowerLit (LInt i) = IRInt i
lowerLit LUnit = IRVoid

resolveType :: IRType -> Lowering IRTypeKind
resolveType (IRType tn) | tn `elem` builtinTypeNames = return $ IRTBuiltin tn
resolveType IRBoxType = return $ IRTBox
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
      IRTDef td -> irtdIsBoxed td

irField :: (Maybe IRTypeDef) -> IRExpr -> Ident -> IRExpr
irField mTd obj fld =
  if fromMaybe False $ irtdIsBoxed <$> mTd
  then IRField (IRUnbox obj) fld
  else IRField obj fld

irCheckVariant :: IRTypeDef -> IRExpr -> Ident -> IRExpr
irCheckVariant td obj var =
  if irtdIsBoxed td
  then IRCheckVariant (IRUnbox obj) var
  else IRCheckVariant obj var

boxExpr :: IRType -> IRExpr -> Lowering IRExpr
boxExpr t e = do
  x <- newVar' (Just "_box")
  tell [ IRBox t x e ]
  return $ IRVar x

matchBoxing :: IRType -> IRType -> IRExpr -> Lowering IRExpr
matchBoxing targetTy incomingTy e = do
  tb <- isBoxType targetTy
  ib <- isBoxType incomingTy
  case (tb, ib) of
    (True, False) -> boxExpr incomingTy e
    (False, True) -> return $ IRUnbox e
    _ -> return e

boxArguments :: [IRType] -> [(IRType, IRExpr)] -> Lowering [IRExpr]
boxArguments ts args =
  mapM (\(targetT, (incomingT, e)) ->
          matchBoxing targetT incomingT e)
    (zip ts args)

spillExpr :: Text -> TExpr -> Lowering Ident
spillExpr n e = do
  e' <- lowerExpr e
  case e' of
    IRVar x -> return x
    _ -> do
      t' <- lowerType $ typeOf e
      x <- newVar' (Just n)
      tell [ IRDef t' x $ Just e' ]
      return x

irCons :: IRType -> Ident -> [IRExpr] -> Lowering IRExpr
irCons t c xs = do
  t' <- resolveType t
  case t' of
    IRTDef td -> do
      let ce = IRCons t c xs
      if irtdIsBoxed td
      then boxExpr t ce
      else return ce
    _ -> error $ "Non data-structure type for constructor! type: " ++ (show t) ++ " cons: " ++ (show c)

lowerExpr' :: TExpr -> Lowering (IRType, IRExpr)
lowerExpr' e = do
  e' <- lowerExpr e
  t <- lowerType (typeOf e)
  return (t, e')

lowerFunType :: Type -> Lowering (IRType, [IRType])
lowerFunType (TFun ts t) = (,) <$> (lowerType t) <*> (mapM lowerType ts)
lowerFunType t = do
  td <- lookupTypeDef t
  case irtdBody td of
    IRFunType t rt -> return (t, rt)
    _ -> error $ "Expected a function type: " ++ (show t)

lowerExpr :: TExpr -> Lowering IRExpr
lowerExpr e =
  case e of
    ELit _ l -> return $ IRLit $ lowerLit l
    EBuiltin _ _ -> error $ "Bare operatior: " ++ (show e)
    ECons t (Ident cn _ _) -> do
      t' <- lowerType t
      irCons t' (mkId cn) []
    ELocal _ x -> return $ IRVar x
    EGlobal _ x -> return $ IRVar x
    EIdent _ _ -> error $ "EIdent found during lowering: " ++ (show e)
    EApp _ (EBuiltin _ b) xs -> do
      xs' <- mapM lowerExpr xs
      let o = case b of
                BAdd -> OpAdd
                BEq  -> OpEq
      return $ IROp o xs'
    EApp t fe xs -> do
      (_, prmTys) <- lowerFunType $ typeOf fe
      xs' <- (boxArguments prmTys) =<< (mapM lowerExpr' xs)
      case fe of
        ECons _ (Ident cn _ _) -> do
          t' <- lowerType t
          irCons t' (mkId cn) xs'
        f -> do
          fx <- spillExpr "_callee" f
          return $ IRCall fx xs'
    ELet _ ls e0 -> do
      mapM_ lowerBinding ls
      lowerExpr e0
    EIf t e0 e1 e2 -> do
      r <- newVar' (Just "_phi")
      t' <- lowerType t
      irDef t' r Nothing
      e0' <- lowerExpr e0
      (_, sts1) <- stmts $ do
        te1' <- lowerExpr' e1
        irSet t' r te1'
      (_, sts2) <- stmts $ do
        te2' <- lowerExpr' e2
        irSet t' r te2'
      tell [ IRIf e0' sts1 sts2 ]
      return $ IRVar r
    ECase t e0 cs -> do
      x <- spillExpr "_matchee" e0
      lowerCases x t cs
    ETup _ _ -> error "Tuples are not supported yet"

lookupTypeDef :: Type -> Lowering IRTypeDef
lookupTypeDef (TCons t _) = do
  tis <- lstTypes <$> get
  case M.lookup t tis of
    Nothing -> error $ "Unresolved type during lowering: " ++ (show t)
    Just td -> return td
lookupTypeDef t = error $ "Invalid type during lowering: " ++ (show t)

lowerType' :: Set Ident -> Type -> Lowering IRType
lowerType' rg (TCons x _) | S.member x rg = return $ IRType x
lowerType' _ t = lowerType t

lowerType :: Type -> Lowering IRType
lowerType (TVar _) = return IRBoxType
lowerType t@(TCons x []) | isBuiltinType t = return $ IRType x
lowerType t = do
  td <- lookupTypeDef t
  return $ IRType $ irtdName td

lowerPattern :: TPat -> IRExpr -> [IRStmt] -> Lowering ([IRExpr], [IRStmt])
lowerPattern (PHole _) _ bs = return ([], bs)
lowerPattern (PLit _ l) path bs = return ([IROp OpEq [path, IRLit $ lowerLit l]], bs)
lowerPattern (PBinding t x) path bs = do
  t' <- lowerType t
  return ([], bs ++ [IRDef t' x $ Just path])
lowerPattern (PCons t c ps) path bs = do
  td <- lookupTypeDef t
  let tn = irtdName td
  case irtdBody td of
    IRFunType _ _ -> error $ "Tried to match a function pointer type with a constructor? "
                         ++ (show c) ++ " : " ++ (show t)
    IRCType _ -> error $ "Tried to match a ctype with a constructor? " ++ (show c) ++ " : " ++ (show t)
    IREnumType _ -> do
      irc <- irCons (IRType tn) c []
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

lowerRecordPattern :: (Maybe IRTypeDef) -> [TPat] -> [IRStmt] -> IRExpr -> [(IRType, Ident)]
                   -> Lowering ([IRExpr], [IRStmt])
lowerRecordPattern mTd ps bs0 path fs =
    foldM (\(cs, bs) ((_, f), p) -> do
            (cs', bs') <- lowerPattern p (irField mTd path f) bs
            return (cs ++ cs', bs'))
    ([], bs0)
    (zip fs ps)

lowerCases :: Ident -> Type -> [TCase] -> Lowering IRExpr
lowerCases matchVar rTy cases = do
  r <- newVar' (Just "_phi")
  rTy' <- lowerType rTy
  irDef rTy' r Nothing
  makeIfElseChain =<< mapM (lowerCase rTy' r) cases
  return $ IRVar r
  where
    lowerCase rTy' r (Case p _ e) = do
      (eCs, bs) <- lowerPattern p (IRVar matchVar) []
      (_, sts) <- stmts $ do
         te' <- lowerExpr' e
         irSet rTy' r te'
      return (eCs, bs ++ sts)
    makeIfElseChain [([], body)] = tell body
    makeIfElseChain [] = tell [ IRPanic "Uncovered match case" ]
    makeIfElseChain ((eCs, body):xs) = do
      (_, sts2) <- stmts $ makeIfElseChain xs
      tell [ IRIf (IROp OpAnd eCs) body sts2 ]

lowerBody :: TExpr -> Lowering ()
lowerBody b = do
  r <- lowerExpr b
  tell [ IRReturn r ]

lowerFunction :: TFunction -> Lowering IRFunc
lowerFunction f = do
  let fty = case fType f of
              MonoType mt -> mt
              PolyType _ pt -> pt
  let (_, retT) = case unFn fty of
                    Nothing -> error "Type of function isn't a arrow type!"
                    Just x -> x
  (_, body) <- stmts $ lowerBody $ fBody f
  argsTs <- mapM (\(x, t) -> ((,) x) <$> (lowerType t)) $ fArgs f
  retT' <- lowerType retT
  let f' = IRFunc { irfName  = fName f
                  , irfPub   = fPub f
                  , irfRetTy = retT'
                  , irfArgs  = argsTs
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
                        _ -> error $ "Polymorphic values are not support yet: " ++ (show x) ++ " : " ++ (show t)
             te' <- lowerExpr' e
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
  let r = IRRecord (bare c) $ zip ts' unnamedFields
  return $ mkTypeDef n rg $ IRStructType r
lowerTypeDef' (TypeDef n _ rg (TBConses cs)) = do
  if allTags
  then return $ mkTypeDef n rg $ IREnumType $ reverse variants
  else do
    rs <- mapM (\(TypeCons c ts) -> do
                    ts' <- mapM (lowerType' rg) ts
                    return $ IRRecord (bare c) $ zip ts' unnamedFields)
           cs
    return $ mkTypeDef n rg $ IRTaggedType rs
  where
    (allTags, variants) =
      foldl (\(a, vs) (TypeCons v ts) -> (a && (null ts), (bare v) : vs)) (True, []) cs
lowerTypeDef' (TypeDef n _ rg (TBAlias (TFun ts t))) = do
  ts' <- mapM (lowerType' rg) ts
  t' <- lowerType' rg t
  return $ mkTypeDef n rg $ IRFunType t' ts'
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
  (vs, inits) <- lowerVals vals
  mapM_ lowerFunction $ funs
  fs <- lstFuncs <$> get
  return $ IRProgram { irpName  = mName m
                     , irpTypes = tds'
                     , irpFuncs = reverse fs
                     , irpVars  = vs
                     , irpInit  = inits }

lowerToIR :: TModule -> IRProgram
lowerToIR m = runLowering $ lowerModule m
