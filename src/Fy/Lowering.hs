module Fy.Lowering
  ( lowerToIR
  ) where

import Fy.Types
import Fy.Ast
import Fy.Ir
import Fy.Typing

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
import Data.List (intersperse, intercalate, partition, find)
import Data.Maybe (fromMaybe, maybeToList)
import Data.Char
import Control.Monad (when, foldM, unless)
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.RWS
import Data.Graph (stronglyConnComp, SCC(..))
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
      EBuiltin t b -> error $ "Bare operatior: " ++ (show e)
      ECons t x -> return $ IRCons (typeName t) x []
      ELocal t x -> return $ IRVar x
      EGlobal t x -> return $ IRVar x
      EIdent _ _ -> error $ "EIdent found during lowering: " ++ (show e)
      EApp t (ECons _ x) xs -> do
        xs' <- mapM lowerExpr xs
        return $ IRCons (typeName t) x xs'
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
      ECase t e cs -> do
        e' <- lowerExpr e
        x <- case e' of
             IRVar x -> return x
             _ -> do
               x <- newVar' (Just "_matchee")
               tell [ IRDef (typeOf e) x $ Just e' ]
               return $ x
        lowerCases x t cs

lookupTypeDef :: Type -> Lowering IRTypeDef
lookupTypeDef t@(TVar _) = error $ "Type variable during lowering: " ++ (show t)
lookupTypeDef t@(TFun _ _) = error $ "Tried to lookup a function type: " ++ (show t)
lookupTypeDef t@(TCons c []) = do
  tds <- lstTypeInsts <$> get
  case M.lookup t tds of
    Nothing -> error $ "Couldn't resolve type: " ++ (show t)
    Just td -> return td
lookupTypeDef t = error $ "Parametric types are not yet supported: " ++ (show t)

lowerCases :: Ident -> IRType -> [TCase] -> Lowering IRExpr
lowerCases x t cs = do
  r <- newVar' (Just "_phi")
  irDef t r Nothing
  makeIfElseChain =<< mapM (lowerCase r) cs
  return $ IRVar r
  where
    lowerCase r (Case p vs e) = do
      (eCs, bs) <- lowerPattern p (IRVar x) []
      (_, sts) <- stmts $ do
         e' <- lowerExpr e
         tell [ IRSet r e' ]
      return (eCs, bs ++ sts)
    lowerPattern :: TPat -> IRExpr -> [IRStmt] -> Lowering ([IRExpr], [IRStmt])
    lowerPattern (PHole _) path bs = return ([], bs)
    lowerPattern (PLit _ l) path bs = return ([IROp OpEq [path, IRLit $ lowerLit l]], bs)
    lowerPattern (PBinding t x) path bs = return ([], bs ++ [IRDef t x $ Just path])
    lowerPattern (PCons t c ps) path bs = do
      td <- lookupTypeDef t
      case td of
        IRCType _ _ -> error $ "Tried to match a ctype with a constructor? " ++ (show c) ++ " : " ++ (show t)
        IREnumType t _ -> return ([IROp OpEq [path, IRCons t c []]], bs)
        IRStructType _ (IRRecord _ fs) -> lowerRecordPattern ps bs path fs
        IRTaggedType t rs -> do
          case find (\(IRRecord c0 _) -> c == c0) rs of
            Nothing -> error $ "Couldn't find constructor `" ++ (show c) ++ "` in type: " ++ (show t)
            Just (IRRecord _ fs) -> do
              (cs, bs') <- lowerRecordPattern ps bs (IRField path c) fs
              return ((IRCheckVariant path t c):cs, bs')
      where
        lowerRecordPattern ps bs path fs =
          foldM (\(cs, bs) ((_, f), p) -> do
                    (cs', bs') <- lowerPattern p (IRField path f) bs
                    return (cs ++ cs', bs'))
            ([], bs)
            (zip fs ps)
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
  let (tArgs, tRet) = case unFn ft of
                        Nothing -> error $ "Non-function type as function head: " ++ (show fx) ++ " : " ++ (show ft)
                        Just r -> r

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
  lowerFunction f
  fs <- lstFuncs <$> get
  return $ IRProgram { irpTypes = types', irpFuncs = reverse fs }

lowerToIR :: [TypeDef] -> TFunction -> IRProgram
lowerToIR tds ast = runLowering $ lowerProgram tds ast
