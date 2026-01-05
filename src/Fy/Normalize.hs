module Fy.Normalize
  (normalize)
  where

import Fy.Types
import Fy.Ast

import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad.State.Strict

data NormSt = NormSt { nstGlobals :: [TBinding]
                     , nstLocals  :: [([TBinding], Set Ident)]
                     , nstNext    :: Int }

type Norm = State NormSt

newVar :: Ident -> Norm Ident
newVar (Ident n ns _) = do
  x <- nstNext <$> get
  modify (\s -> s { nstNext = x + 1 })
  return $ Ident n ns $ Just x

runNorm :: Norm a -> a
runNorm m = evalState m $ NormSt { nstGlobals = []
                                 , nstLocals  = []
                                 , nstNext    = 0 }

addGlobal :: TBinding -> Norm ()
addGlobal g =
  modify (\s -> s { nstGlobals = g : (nstGlobals s) })

addDep :: Ident -> Norm ()
addDep x =
  modify (\s ->
            case nstLocals s of
              [] -> error $ "Empty locals scope! Tried to add: " ++ (show x)
              (ls, deps):lss -> s { nstLocals = (ls, S.insert x deps):lss })

addLocal :: TBinding -> Norm ()
addLocal l =
  modify (\s ->
            case nstLocals s of
              [] -> error $ "Empty locals scope! Tried to add: " ++ (show l)
              (ls, deps):lss -> s { nstLocals = ((l:ls), deps):lss })

pushScope :: Norm ()
pushScope = modify (\s -> s { nstLocals = ([], S.empty) : (nstLocals s) })

popScope :: Norm ([TBinding], Set Ident)
popScope = do
  ls <- (head . nstLocals) <$> get
  modify (\s -> s { nstLocals = tail $ nstLocals s })
  return ls

block :: TExpr -> Norm (TExpr, Set Ident)
block e = do
  (ls, deps) <- popScope
  case ls of
    [] -> return (e, deps)
    _ -> return (ELet (typeOf e) ls e, deps)

normExpr :: TExpr -> Norm TExpr
normExpr e =
  case e of
    -- Lift the lambda-function into a global and create a closure instead
    ELam t xs deps caps e0 -> do
      fn <- newVar $ mkId "_clof"
      (e0', deps') <- block e0
      let f = Function fn (toPoly t) xs caps Private (S.union deps deps') e0'
      addGlobal $ bindingFromFunction f
      addDep fn
      return $ EClo t fn $ map (\(_, _, ce) -> ce) caps
    -- Lift any local bindings to the nearest block, and function to globals
    ELet t bs e0 -> do
      mapM_ (\b -> do
               case bBody b of
                 Val ve -> addLocal b
                 Fun f -> do
                   fn' <- newVar $ fName f
                   addDep fn'
                   addGlobal $ bindingFromFunction $ f { fName = fn' }
                   let caps = map (\(_, _, e) -> e) $ fEnv f
                   addLocal $ b { bBody = Val (EClo (innerType $ bType b) fn' caps) }
                 )
        bs
      return e0
    _ -> return e

normFunction :: TFunction -> Norm TFunction
normFunction f = do
  (e', deps) <- block (fBody f)
  return $ f { fBody = e', fDeps = S.union deps $ fDeps f }

normBinding :: TBinding -> Norm TBinding
normBinding = return

pass :: AstVisitor Norm Type
pass = newVisitor { avPreExpr =
                    (\e -> do
                       case e of
                         ELam _ _ _ _ _ -> pushScope >> (return e)
                         _ -> return e)
                  , avPostExpr     = normExpr
                  , avPreFunction  = (\e -> pushScope >> (return e))
                  , avPostFunction = normFunction
                  , avPostBinding  = normBinding }

normGlobal :: TBinding -> Norm ()
normGlobal b = do
  b' <- case bBody b of
          Val e -> do
            pushScope
            e' <- visitExpr pass e
            (e'', deps) <- block e'
            return $ b { bBody = Val e'', bDeps = S.union deps $ bDeps b }
          Fun f -> do
            f' <- visitFunction pass f
            return $ b { bBody = Fun f', bDeps = fDeps f' }
  addGlobal $ b'

normalize :: TModule -> TModule
normalize m = runNorm $ do
  modify (\s -> s { nstNext = mNextId m })
  mapM_ normGlobal $ mItems m
  bs' <- nstGlobals <$> get
  nid' <- nstNext <$> get
  return $ m { mItems = reverse bs'
             , mNextId = nid' }
