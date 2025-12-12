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
import Data.Graph (stronglyConnComp, SCC(..))

data LoweringSt = LoweringSt { lstNext  :: Int
                             , lstFuncs :: [IRFunc]
                             , lstTypes :: M.HashMap Ident IRTypeDef }

type Lowering = RWS () [IRStmt] LoweringSt


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

irDef' :: IRType -> Ident -> (Maybe IRExpr) -> [IRStmt]
irDef' t x v =
  if t == irtUnit
  then []
  else [ IRDef t x v ]

irDef :: IRType -> Ident -> (Maybe IRExpr) -> Lowering ()
irDef t x v = tell $ irDef' t x v

lowerBinding :: TBinding -> Lowering ()
lowerBinding l@(Binding t x _ _ (Val e)) = do
  e' <- lowerExpr e
  case t of
    MonoType t0 -> do
      t0' <- lowerType t0
      irDef t0' x (Just e')
    _ -> error $ "Can't lower a polytype local: " ++ (show l)
lowerBinding (Binding { bBody = Fun f }) = lowerFunction f >> return ()

stmts :: Lowering a -> Lowering (a, [IRStmt])
stmts m = censor (const []) $ listen m

filterVoids :: [IRExpr] -> [IRExpr]
filterVoids = filter (\x -> case x of
                              IRLit IRVoid -> False
                              _            -> True)

lowerLit :: Lit -> IRLit
lowerLit (LInt i) = IRInt i
lowerLit LUnit = IRVoid

lowerExpr :: TExpr -> Lowering IRExpr
lowerExpr e =
  if (typeOf e) == tUnit
  then return $ IRLit IRVoid
  else do
    case e of
      ELit _ l -> return $ IRLit $ lowerLit l
      EBuiltin _ _ -> error $ "Bare operatior: " ++ (show e)
      ECons t x -> do
        t' <- lowerType t
        return $ IRCons t' x []
      ELocal _ x -> return $ IRVar x
      EGlobal _ x -> return $ IRVar x
      EIdent _ _ -> error $ "EIdent found during lowering: " ++ (show e)
      EApp t (ECons _ x) xs -> do
        xs' <- mapM lowerExpr xs
        t' <- lowerType t
        return $ IRCons t' x xs'
      EApp _ (EBuiltin _ b) xs -> do
        xs' <- filterVoids <$> mapM lowerExpr xs
        let o = case b of
                  BAdd -> OpAdd
                  BEq  -> OpEq
        return $ IROp o xs'
      EApp _ f xs -> do
        f' <- lowerExpr f
        xs' <- filterVoids <$> mapM lowerExpr xs
        case f' of
          IRVar fx -> do
            return $ IRCall fx xs'
          _ -> error $ "Lowering non-direct calls are not supported yet: " ++ (show e)
      ELet _ ls e0 -> do
        mapM_ lowerBinding ls
        lowerExpr e0
      EIf t e0 e1 e2 -> do
        r <- newVar' (Just "_phi")
        t' <- lowerType t
        irDef t' r Nothing
        e0' <- lowerExpr e0
        (_, sts1) <- stmts $ do
          e1' <- lowerExpr e1
          tell [ IRSet r e1' ]
        (_, sts2) <- stmts $ do
          e2' <- lowerExpr e2
          tell [ IRSet r e2' ]
        tell [ IRIf e0' sts1 sts2 ]
        return $ IRVar r
      ECase t e0 cs -> do
        e0' <- lowerExpr e0
        x <- case e0' of
               IRVar x -> return x
               _ -> do
                 x <- newVar' (Just "_matchee")
                 t0 <- lowerType (typeOf e0)
                 tell [ IRDef t0 x $ Just e0' ]
                 return $ x
        lowerCases x t cs
      ETup _ _ -> error "Tuples are not supported yet"

lookupTypeDef :: Type -> Lowering IRTypeDef
lookupTypeDef (TCons t []) = do
  tis <- lstTypes <$> get
  case M.lookup t tis of
    Nothing -> error $ "Unresolved type during lowering: " ++ (show t)
    Just td -> return td
lookupTypeDef t = error $ "Invalid type during lowering: " ++ (show t)

lowerType :: Type -> Lowering IRType
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
    IREnumType _ -> return ([IROp OpEq [path, IRCons (IRType tn) c []]], bs)
    IRStructType (IRRecord _ fs) -> lowerRecordPattern ps bs path fs
    IRTaggedType rs -> do
      case find (\(IRRecord c0 _) -> c == c0) rs of
        Nothing -> error $ "Couldn't find constructor `" ++ (show c) ++ "` in type: " ++ (show t)
        Just (IRRecord _ fs) -> do
          (cs, bs') <- lowerRecordPattern ps bs (IRField path c) fs
          return ((IRCheckVariant path tn c):cs, bs')
    IRTypeAlias (IRType t') ->
      lowerPattern (PCons (TCons t' []) c ps) path bs

lowerRecordPattern :: [TPat] -> [IRStmt] -> IRExpr -> [(IRType, Ident)]
                   -> Lowering ([IRExpr], [IRStmt])
lowerRecordPattern ps bs0 path fs =
    foldM (\(cs, bs) ((_, f), p) -> do
            (cs', bs') <- lowerPattern p (IRField path f) bs
            return (cs ++ cs', bs'))
    ([], bs0)
    (zip fs ps)

lowerCases :: Ident -> Type -> [TCase] -> Lowering IRExpr
lowerCases matchVar rTy cases = do
  r <- newVar' (Just "_phi")
  rTy' <- lowerType rTy
  irDef rTy' r Nothing
  makeIfElseChain =<< mapM (lowerCase r) cases
  return $ IRVar r
  where
    lowerCase r (Case p _ e) = do
      (eCs, bs) <- lowerPattern p (IRVar matchVar) []
      (_, sts) <- stmts $ do
         e' <- lowerExpr e
         tell [ IRSet r e' ]
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
  let (_, retT) = case fType f of
                    MonoType fty -> case unFn fty of
                                      Nothing -> error "Type of function isn't a arrow type!"
                                      Just x -> x
                    PolyType _ _ -> error $ "Polymorphic functions are not supported: " ++ (show $ fType f)
  (_, body) <- stmts $ lowerBody $ fBody f
  let args = filter (((/=) tUnit) . snd) $ fArgs f
  argsTs <- mapM (\(x, t) -> ((,) x) <$> (lowerType t)) $ args
  retT' <- lowerType retT
  let f' = IRFunc { irfName  = fName f
                  , irfPub   = fPub f
                  , irfRetTy = retT'
                  , irfArgs  = argsTs
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
             e' <- lowerExpr e
             t0' <- lowerType t0
             tell [ IRSet x e' ]
             return $ IRVarDecl x p t0'
           _ -> error $ "Function binding passed to lowerVals: " ++ (show b))
    bs

mkTypeDef :: Ident -> IRTypeBody -> IRTypeDef
mkTypeDef n b = IRTypeDef n S.empty False b

lowerTypeDef :: Set Ident -> TypeDef -> Lowering IRTypeDef
lowerTypeDef recGroup td = do
  td' <- lowerTypeDef' td
  return $ annotateType recGroup td'

lowerTypeDef' :: TypeDef -> Lowering IRTypeDef
lowerTypeDef' (TypeDef n _ (TBCType ct)) = return $ mkTypeDef n $ IRCType ct
lowerTypeDef' (TypeDef _ _ (TBConses [])) = error $ "Zero types are not supported yet"
lowerTypeDef' (TypeDef n _ (TBConses [(TypeCons c ts)])) = do
  ts' <- mapM lowerType ts
  let r = IRRecord c $ zip ts' unnamedFields
  return $ mkTypeDef n $ IRStructType r
lowerTypeDef' (TypeDef n _ (TBConses cs)) = do
  if allTags
  then return $ mkTypeDef n $ IREnumType $ reverse variants
  else do
    rs <- mapM (\(TypeCons c ts) -> do
                    ts' <- mapM lowerType ts
                    return $ IRRecord c $ zip ts' unnamedFields)
           cs
    return $ mkTypeDef n $ IRTaggedType rs
  where
    (allTags, variants) =
      foldl (\(a, vs) (TypeCons v ts) -> (a && (null ts), v : vs)) (True, []) cs
lowerTypeDef' (TypeDef n _ (TBAlias t)) = do
  t' <- lowerType t
  return $ mkTypeDef n $ IRTypeAlias t'

annotateType :: Set Ident -> IRTypeDef -> IRTypeDef
annotateType recGroup (IRTypeDef tn _ _ body) =
  IRTypeDef tn recGroup isBoxed body
  where
    isBoxed =
      if S.null recGroup
      then
        case body of
          -- TODO: Add a heuristic for when not to box structs and tagged types
          IRStructType _ -> True
          IRTaggedType _ -> True
          _ -> False
      else True

lowerTypeDefs :: [TypeDef] -> Lowering [IRTypeDef]
lowerTypeDefs tds = do
  tds' <- concat <$> mapM (\scc ->
                             case scc of
                               NECyclicSCC xs ->
                                 error $ "Recursive types are not supported yet: " ++ (show xs)
                               AcyclicSCC td -> do
                                 td' <- lowerTypeDef S.empty td
                                 return [td'])
                       (stronglyConnComp $ map typeDepGraph tds)
  modify (\s -> s { lstTypes = M.fromList $ map (\t -> (irtdName t, t)) tds' })
  return tds'
  where
    typeDepGraph td@(TypeDef tn _ (TBConses cs)) = (td, tn, concat $ map consesDeps cs)
    typeDepGraph td@(TypeDef tn _ (TBAlias t)) = (td, tn, typeDeps t)
    typeDepGraph td = (td, tdName td, [])
    consesDeps (TypeCons _ fs) = concat $ map typeDeps fs
    typeDeps (TVar _) = []
    typeDeps (TCons t ts) = t : (concat $ map typeDeps ts)
    typeDeps (TFun ts t) = (typeDeps t) ++ (concat $ map typeDeps ts)

-- TODO: We should probably split up lowering into two phases:
-- - 1: Instanciate all functions and types
-- - 2: Then lower the concrete stuff, that way we can deal properly with boxing
lowerModule :: TModule -> Lowering IRProgram
lowerModule m = do
  tds' <- lowerTypeDefs $ mTypeDefs m
  let (vals, funs) = partitionWith (\b ->
                                      case b of
                                        Binding { bBody = (Fun f) } -> Right f
                                        _ -> Left b)
                         (mItems m)
  (vs, inits) <- lowerVals vals
  fs <- mapM lowerFunction $ funs
  return $ IRProgram { irpName  = mName m
                     , irpTypes = tds'
                     , irpFuncs = reverse fs
                     , irpVars  = vs
                     , irpInit  = inits }

lowerToIR :: TModule -> IRProgram
lowerToIR m = runLowering $ lowerModule m
