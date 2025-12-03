module Fy.Lowering
  ( lowerToIR
  ) where


import Fy.Util
import Fy.Types
import Fy.Ast
import Fy.Ir
import Fy.Typing

import Prelude hiding (lookup, lines)
import Data.Text (Text)
import qualified Data.Text as T
import Data.List (intersperse, find, elemIndex)
import Data.Maybe
import Control.Monad
import Control.Monad.State
import Control.Monad.RWS
import qualified Data.HashMap.Strict as M

data LoweringSt = LoweringSt { lstNext  :: Int
                             , lstFuncs :: [IRFunc]
                             , lstKnownTypes :: M.HashMap Ident TypeDef
                             , lstTypeInsts  :: M.HashMap Type IRTypeDef
                             , lstKnownFuncs :: M.HashMap Ident TFunction
                             , lstFuncInsts  :: M.HashMap (Ident, Type) IRFunc }

type Lowering = RWS () [IRStmt] LoweringSt


runLowering :: Lowering a -> a
runLowering m = fst $ evalRWS m () $
  LoweringSt { lstNext  = 0
             , lstFuncs = []
             , lstTypeInsts = M.empty
             , lstKnownTypes = M.empty
             , lstFuncInsts = M.empty
             , lstKnownFuncs = M.empty
             }

newVar' :: (Maybe Text) -> Lowering Ident
newVar' t = do
  x <- lstNext <$> get
  modify (\s -> s { lstNext = x + 1 } )
  return $ Ident (fromMaybe "__" t) [] (Just x)

encodeType :: TypeScheme -> Text
encodeType t =
  T.concat $
    case t of
        (MonoType t0) -> encodeType' [] t0
        (PolyType vs t0) -> ["S", T.show $ length vs] ++ encodeType' vs t0
  where
    encodeType' :: [TyVar] -> Type -> [Text]
    encodeType' vs (TVar v) =
      case elemIndex v vs of
        Nothing -> error $ "Tried to encode a type with a free variable"
        Just i -> [ "V", T.show i ]
    encodeType' _ (TCons (Ident "int" [] Nothing) []) = ["i"]
    encodeType' _ (TCons (Ident "bool" [] Nothing) []) = ["b"]
    encodeType' _ (TCons (Ident "()" [] Nothing) []) = ["_"]
    encodeType' vs (TCons c cs) =
      let cs' = concatMap (encodeType' vs) cs
          n0 = canonicalId c
          n = [ "N", T.show $ T.length n0, canonicalId c ]
      in if null cs
         then n
         else [ "I", T.show $ length cs ] ++ n ++ cs'
    encodeType' vs (TFun ts t0) =
      let ts' = concatMap (encodeType' vs) ts
          t0' = encodeType' vs t0
      in [ "F", T.show $ length ts ] ++ ts' ++ t0'

irDef' :: IRType -> Ident -> (Maybe IRExpr) -> [IRStmt]
irDef' t x v =
  if t == irtUnit
  then []
  else [ IRDef t x v ]

irDef :: IRType -> Ident -> (Maybe IRExpr) -> Lowering ()
irDef t x v = tell $ irDef' t x v

registerFun :: TFunction -> Lowering ()
registerFun f =
  modify (\s -> s { lstKnownFuncs = M.insert (fName f) f (lstKnownFuncs s) } )

lowerBinding :: TBinding -> Lowering ()
lowerBinding l@(Binding t x _ (Val e)) = do
  e' <- lowerExpr e
  case t of
    MonoType t0 -> do
      t0' <- lowerType t0
      irDef t0' x (Just e')
    _ -> error $ "Can't lower a polytype local: " ++ (show l)
lowerBinding (Binding _ _ _ (Fun f)) = registerFun f

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
            fx' <- instanciateFunc fx (typeOf f)
            return $ IRCall fx' xs'
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
lookupTypeDef t@(TVar _) = error $ "Type variable during lowering: " ++ (show t)
lookupTypeDef t@(TFun _ _) = error $ "Tried to lookup a function type: " ++ (show t)
lookupTypeDef t@(TCons c ts) = do
  tis <- lstTypeInsts <$> get
  case M.lookup t tis of
    Nothing -> do
        tds <- lstKnownTypes <$> get
        case M.lookup c tds of
          Nothing -> error $ "Couldn't resolve type: " ++ (show t)
          Just td -> do
            td' <- instanciateType ts td
            modify (\s -> s { lstTypeInsts = M.insert t td' $ lstTypeInsts s })
            return td'
    Just td -> return td

lowerType :: Type -> Lowering IRType
lowerType (TCons x@(Ident "int" [] Nothing) []) = return $ IRType x
lowerType (TCons x@(Ident "bool" [] Nothing) []) = return $ IRType x
lowerType (TCons x@(Ident "()" [] Nothing) []) = return $ IRType x
lowerType t = do
  td <- lookupTypeDef t
  return $ IRType $ typeDefName td

instanciateType :: [Type] -> TypeDef -> Lowering IRTypeDef
instanciateType ts td@(TypeDef tn _ _) = do
  let ss = Subst $ M.fromList $ zip [0 :: Int ..] ts
  let td' = subst ss td
  let instSuffix = T.concat $ "_" : (intersperse "_" $ map encodeType $ map MonoType $ tdParams td')
  lowerTypeDef $ td' { tdName = (tn `suffixId` instSuffix) }

lowerPattern :: TPat -> IRExpr -> [IRStmt] -> Lowering ([IRExpr], [IRStmt])
lowerPattern (PHole _) _ bs = return ([], bs)
lowerPattern (PLit _ l) path bs = return ([IROp OpEq [path, IRLit $ lowerLit l]], bs)
lowerPattern (PBinding t x) path bs = do
  t' <- lowerType t
  return ([], bs ++ [IRDef t' x $ Just path])
lowerPattern (PCons t c ps) path bs = do
  td <- lookupTypeDef t
  case td of
    IRCType _ _ -> error $ "Tried to match a ctype with a constructor? " ++ (show c) ++ " : " ++ (show t)
    IREnumType tn _ -> return ([IROp OpEq [path, IRCons (IRType tn) c []]], bs)
    IRStructType _ (IRRecord _ fs) -> lowerRecordPattern ps bs path fs
    IRTaggedType tn rs -> do
      case find (\(IRRecord c0 _) -> c == c0) rs of
        Nothing -> error $ "Couldn't find constructor `" ++ (show c) ++ "` in type: " ++ (show t)
        Just (IRRecord _ fs) -> do
          (cs, bs') <- lowerRecordPattern ps bs (IRField path c) fs
          return ((IRCheckVariant path tn c):cs, bs')

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

instanciateFunc :: Ident -> Type -> Lowering Ident
instanciateFunc fx ft = do
  when (isNothing $ unFn ft) $ do
    error $ "Non-function type as function head: " ++ (show fx) ++ " : " ++ (show ft)
  st <- get
  case M.lookup (fx, ft) (lstFuncInsts st) of
    Just f -> return $ irfName f
    Nothing -> do
        case M.lookup fx (lstKnownFuncs st) of
          Nothing -> error $ "Tried to instanciate unknown function: " ++ (show fx)
          Just f ->
            case fType f of
              MonoType _ -> do
                f' <- lowerFunction f
                let fx' = irfName f'
                modify (\s -> s { lstFuncInsts = M.insert (fx', ft) f' (lstFuncInsts s) })
                return fx'
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
                    f'' <- lowerFunction $ f' { fName = fx' }
                    modify (\s -> s { lstFuncInsts = M.insert (fx', ft) f'' (lstFuncInsts s) })
                    return fx'

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
                  , irfRetTy = retT'
                  , irfArgs  = argsTs
                  , irfBody  = body }
  modify (\s -> s { lstFuncs = f' : (lstFuncs s) })
  return f'

lowerTypeDef :: TypeDef -> Lowering IRTypeDef
lowerTypeDef (TypeDef n _ (TBCType ct)) = return $ IRCType n ct
lowerTypeDef (TypeDef _ _ (TBConses [])) = error $ "Zero types are not supported yet"
lowerTypeDef (TypeDef n _ (TBConses [(TypeCons c ts)])) = do
  ts' <- mapM lowerType ts
  let r = IRRecord c $ zip ts' unnamedFields
  return $ IRStructType n r
lowerTypeDef (TypeDef n _ (TBConses cs)) = do
  if allTags
  then return $ IREnumType n $ reverse variants
  else do
    rs <- mapM (\(TypeCons c ts) -> do
                    ts' <- mapM lowerType ts
                    return $ IRRecord c $ zip ts' unnamedFields)
           cs
    return $ IRTaggedType n rs
  where
    (allTags, variants) =
      foldl (\(a, vs) (TypeCons v ts) -> (a && (null ts), v : vs)) (True, []) cs

lowerVals :: [TBinding] -> Lowering ([IRVarDecl], [IRStmt])
lowerVals bs = stmts $
  mapM (\b ->
          case b of
           (Binding t x _ (Val e)) -> do
             let t0 = case t of
                        MonoType mt -> mt
                        _ -> error $ "Polymorphic values are not support yet: " ++ (show x) ++ " : " ++ (show t)
             e' <- lowerExpr e
             t0' <- lowerType t0
             tell [ IRSet x e' ]
             return $ IRVarDecl x t0'
           _ -> error $ "Function binding passed to lowerVals: " ++ (show b))
    bs


lowerModule :: TModule -> Lowering IRProgram
lowerModule m = do
  let tds = M.fromList $ map (\t@(TypeDef tn _ _) -> (tn, t)) $ mTypeDefs m
  modify (\s -> s { lstKnownTypes =  M.union (lstKnownTypes s) tds })
  let (vals, funs) = partitionWith (\b ->
                                      case b of
                                        Binding _ _ _ (Fun f) -> Right f
                                        _ -> Left b)
                         (mItems m)
  mapM_ registerFun funs
  (vs, inits) <- lowerVals vals
  _ <- instanciateFunc (mkId "main") (TFun [tUnit] tUnit)
  fs <- lstFuncs <$> get
  tyInsts <- lstTypeInsts <$> get
  return $ IRProgram { irpName  = mName m
                     , irpTypes = M.elems tyInsts
                     , irpFuncs = reverse fs
                     , irpVars  = vs
                     , irpInit  = inits }

lowerToIR :: TModule -> IRProgram
lowerToIR m = runLowering $ lowerModule m
