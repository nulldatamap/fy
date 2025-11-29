module Fy.Lowering
  ( lowerToIR
  ) where


import Fy.Types
import Fy.Ast
import Fy.Ir
import Fy.Typing

import Prelude hiding (lookup, lines)
import Data.Text (Text)
import qualified Data.Text as T
import Data.List (find)
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
    MonoType t0 -> irDef t0 x (Just e')
    _ -> error $ "Can't lower a polytype local: " ++ (show l)
lowerLocal (Local _ x _ (Fun f)) =
  modify (\s -> s { lstKnownFuncs = M.insert x f (lstKnownFuncs s) } )

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
      ECons t x -> return $ IRCons (typeName t) x []
      ELocal _ x -> return $ IRVar x
      EGlobal _ x -> return $ IRVar x
      EIdent _ _ -> error $ "EIdent found during lowering: " ++ (show e)
      EApp t (ECons _ x) xs -> do
        xs' <- mapM lowerExpr xs
        return $ IRCons (typeName t) x xs'
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
        mapM_ lowerLocal ls
        lowerExpr e0
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
      ECase t e0 cs -> do
        e0' <- lowerExpr e0
        x <- case e0' of
               IRVar x -> return x
               _ -> do
                 x <- newVar' (Just "_matchee")
                 tell [ IRDef (typeOf e0) x $ Just e0' ]
                 return $ x
        lowerCases x t cs
      ETup _ _ -> error "Tuples are not supported yet"

lookupTypeDef :: Type -> Lowering IRTypeDef
lookupTypeDef t@(TVar _) = error $ "Type variable during lowering: " ++ (show t)
lookupTypeDef t@(TFun _ _) = error $ "Tried to lookup a function type: " ++ (show t)
lookupTypeDef t@(TCons _ []) = do
  tds <- lstTypeInsts <$> get
  case M.lookup t tds of
    Nothing -> error $ "Couldn't resolve type: " ++ (show t)
    Just td -> return td
lookupTypeDef t = error $ "Parametric types are not yet supported: " ++ (show t)

lowerPattern :: TPat -> IRExpr -> [IRStmt] -> Lowering ([IRExpr], [IRStmt])
lowerPattern (PHole _) _ bs = return ([], bs)
lowerPattern (PLit _ l) path bs = return ([IROp OpEq [path, IRLit $ lowerLit l]], bs)
lowerPattern (PBinding t x) path bs = return ([], bs ++ [IRDef t x $ Just path])
lowerPattern (PCons t c ps) path bs = do
  td <- lookupTypeDef t
  case td of
    IRCType _ _ -> error $ "Tried to match a ctype with a constructor? " ++ (show c) ++ " : " ++ (show t)
    IREnumType tn _ -> return ([IROp OpEq [path, IRCons tn c []]], bs)
    IRStructType _ (IRRecord _ fs) -> lowerRecordPattern ps bs path fs
    IRTaggedType tn rs -> do
      case find (\(IRRecord c0 _) -> c == c0) rs of
        Nothing -> error $ "Couldn't find constructor `" ++ (show c) ++ "` in type: " ++ (show t)
        Just (IRRecord _ fs) -> do
          (cs, bs') <- lowerRecordPattern ps bs (IRField path c) fs
          return ((IRCheckVariant path tn c):cs, bs')

lowerRecordPattern :: [TPat] -> [IRStmt] -> IRExpr -> [(Type, Ident)]
                   -> Lowering ([IRExpr], [IRStmt])
lowerRecordPattern ps bs0 path fs =
    foldM (\(cs, bs) ((_, f), p) -> do
            (cs', bs') <- lowerPattern p (IRField path f) bs
            return (cs ++ cs', bs'))
    ([], bs0)
    (zip fs ps)

lowerCases :: Ident -> IRType -> [TCase] -> Lowering IRExpr
lowerCases matchVar rTy cases = do
  r <- newVar' (Just "_phi")
  irDef rTy r Nothing
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
                    fx' <- refreshName $ fName f'
                    f'' <- lowerFunction $ f' { fName = fx' }
                    modify (\s -> s { lstFuncInsts = M.insert (fx', ft) f'' (lstFuncInsts s) })
                    return fx'
  where
    refreshName (Ident x ns mI) = do
      let x' = case mI of
                Nothing -> x
                Just i -> T.concat [ x, "_", (T.pack $ show i), "_inst__" ]
      (Ident _ _ i') <- newVar
      return $ Ident x' ns i'

lowerFunction :: TFunction -> Lowering IRFunc
lowerFunction f = do
  let (_, retT) = case fType f of
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

lowerType :: TypeDef -> Lowering IRTypeDef
lowerType td@(TypeDef n _) = do
  x <- lowerType' td
  modify (\s -> s { lstTypeInsts = M.insert (TCons n []) x $ lstTypeInsts s })
  return x
lowerType' :: TypeDef -> Lowering IRTypeDef
lowerType' (TypeDef n (TBCType ct)) = return $ IRCType n ct
lowerType' (TypeDef _ (TBConses [])) = error $ "Zero types are not supported yet"
lowerType' (TypeDef n (TBConses [(TypeCons c ts)])) = do
  let r = IRRecord c $ zip ts unnamedFields
  return $ IRStructType n r
lowerType' (TypeDef n (TBConses cs)) = do
  if allTags
  then return $ IREnumType n $ reverse variants
  else return $ IRTaggedType n rs
  where
    (allTags, variants) =
      foldl (\(a, vs) (TypeCons v ts) -> (a && (null ts), v : vs)) (True, []) cs
    rs = map (\(TypeCons c ts) -> IRRecord c $ zip ts unnamedFields) cs

lowerProgram :: [TypeDef] -> TFunction -> Lowering IRProgram
lowerProgram types f = do
  types' <- mapM lowerType types
  _ <- lowerFunction f
  fs <- lstFuncs <$> get
  return $ IRProgram { irpTypes = types', irpFuncs = reverse fs }

lowerToIR :: [TypeDef] -> TFunction -> IRProgram
lowerToIR tds ast = runLowering $ lowerProgram tds ast
