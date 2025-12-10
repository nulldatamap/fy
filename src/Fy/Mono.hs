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

instanciate :: Substitutable a => [Type] -> a -> a
instanciate ts x = subst (Subst $ M.fromList $ zip [0 :: Int ..] ts) x

instanciateType :: [Type] -> TypeDef -> Mono TypeDef
instanciateType [] td = return td
instanciateType ts td@(TypeDef tn _ _) = do
  let td' = instanciate ts td
  let instSuffix = T.concat $ "_" : (intersperse "_" $ map encodeType $ map MonoType $ tdParams td')
  return $ td' { tdName = (tdName td') `suffixId` instSuffix}

lookupTypeDef :: Type -> Mono TypeDef
lookupTypeDef t@(TVar _) = error $ "Unresolved type variable during monomorphisation: " ++ (show t)
lookupTypeDef t@(TFun ts rt) = do
  tis <- mstTypeInsts <$> get
  case M.lookup t tis of
    Nothing -> do
      let td = TypeDef (mkId $ encodeType $ MonoType t) [] $ TBAlias t
      modify (\s -> s { mstTypeInsts = M.insert t td $ mstTypeInsts s })
      return td
    Just td -> return td
lookupTypeDef t@(TCons c ts) = do
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
tryInstanciateFunc fx ft = do
  mx <- instanciateFunc' fx ft
  case mx of
    Nothing -> return fx
    Just x -> return x

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
              MonoType _ -> do
                modify (\s -> s { mstFuncInsts = M.insert (fx, ft) f (mstFuncInsts s) })
                return $ Just fx
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
                    modify (\s -> s { mstFuncInsts = M.insert (fx', ft) f' (mstFuncInsts s) })
                    return $ Just fx'

-- monoBinding :: TBinding -> Mono TBinding
-- monoBinding b@(Binding { bBody = Val e }) = do
--   e' <- monoExpr e
--   return $ b { bBody = Val e' }
-- monoBinding b@(Binding { bType = MonoType t, bBody = Fun f }) = do
--   f' <- monoFunction f
--   return $ b { bBody = Fun f' }
monoBinding b = return b

monoModule :: TModule -> Mono TModule
monoModule m = do
  let tds = M.fromList $ map (\t@(TypeDef tn _ _) -> (tn, t)) $ mTypeDefs m
  modify (\s -> s { mstKnownTypes =  M.union (mstKnownTypes s) tds })
  -- TODO: All exported polymorphic functions should get realized as "boxed" parameter functions
  mapM_ (\x ->
           case x of
             Binding { bBody = Fun f } -> (registerFun f) >> return ()
             _ -> return ())
    (mItems m)
  _ <- instanciateFunc (mkId "main") (TFun [tUnit] tUnit)
  bs' <- mapM monoBinding $ mItems m
  return $ m { mItems = bs' }

monomorphise :: TModule -> TModule
monomorphise m = runMono $ monoModule m
