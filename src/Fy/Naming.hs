{-# LANGUAGE OverloadedStrings, FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveAnyClass, DeriveGeneric, StandaloneDeriving, FunctionalDependencies, MultiParamTypeClasses #-}
module Fy.Naming
  ( namingCheck
  ) where

import Fy.Types
import Fy.Ast

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
import Data.List (intersperse, intercalate, partition)
import Data.Maybe (fromMaybe, maybeToList)
import Data.Char
import Control.Monad (when, foldM, unless)
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.RWS
import Data.Graph (stronglyConnComp, SCC(..))
import qualified Data.HashMap.Strict as M

data NameKind = NKLocal Int
              | NKGlobal
              | NKCons
  deriving Show

data NameEntry = NameEntry { neName  :: Ident
                           , neKind  :: NameKind }
  deriving Show

type NameMap = M.HashMap Ident NameEntry
type TypeDefMap = M.HashMap Ident (Maybe TypeBody)

data NamingSt = NamingSt { nstNext   :: Int
                         , nstDepth  :: Int
                         , nstDeps   :: Set Ident
                         , nstTypes  :: TypeDefMap
                         , nstScope  :: NameMap }

data NamingError = UndefinedName Ident
                 | UndefinedType Ident
                 | InvalidCapture Ident
                 | DuplicateNames [Ident]
                 | InvalidPattern UPat
  deriving Show

type Naming = StateT NamingSt (Except NamingError)



instance Context Naming Ident NameEntry NamingError where
  getContext = nstScope <$> get
  modifyContext f = modify (\s -> s { nstScope = f $ nstScope s })
  undefinedVar = throwError . UndefinedName

uniqId :: Ident -> Naming Ident
uniqId (Ident x ns _) = do
  n <- nstNext <$> get
  modify (\s -> s { nstNext = n + 1 })
  return $ Ident x ns (Just n)

block :: Naming a -> Naming (a, Set Ident)
block x = do
  oldSt <- get
  modify (\s -> s { nstDeps = S.empty })
  r <- x
  st <- get
  modify (\s -> s { nstDeps = nstDeps oldSt })
  return (r, nstDeps st)

addDeps :: Ident -> Naming ()
addDeps x = modify (\s -> s { nstDeps = S.insert x (nstDeps s) })

runNaming :: NameMap -> Naming a -> Either NamingError a
runNaming gs n = runExcept (evalStateT n st)
  where
    st = NamingSt { nstNext = 0, nstScope = gs, nstDepth = 0 }

withVars :: [(Ident, Ident)] -> Naming a -> Naming a
withVars xs m = do
    d <- nstDepth <$> get
    scoped (map (\(x, x') -> (x, NameEntry x' (NKLocal d))) xs) m

scopedVars' :: [Ident] -> Naming a -> Naming ([Ident], a)
scopedVars' xs m = do
    xs' <- mapM uniqId xs
    d <- nstDepth <$> get
    scoped (map (\(x, x') -> (x, NameEntry x' (NKLocal d))) $ zip xs xs') $ ((,) xs') <$> m

scopedVars :: [Ident] -> Naming a -> Naming a
scopedVars xs m = snd <$> scopedVars' xs m

checkLocals :: [Local ()] -> UExpr -> Naming UExpr
checkLocals ls e = do
  (ls', e') <- scopedVars (map (\(Local { lName = x }) -> x) ls) $ do
    ls' <- mapM checkLocal ls
    e' <- checkExpr e
    return (ls', e')
  return $ ELet () ls' e'
checkLocal (Local t x _ (Val e)) = do
  (NameEntry x' _) <- lookup x
  (e', deps) <- block $ checkExpr e
  return $ Local t x' deps (Val e')
checkLocal (Local t x _ (Fun f)) = do
   (NameEntry x' _) <- lookup x
   f <- checkFunction x' (map fst $ fArgs f) (fBody f)
   return $ Local t x' (S.empty) (Fun f)

checkPat :: UPat -> Naming (UPat, [(Ident, Ident)])
checkPat p = do
  (p', _, vs) <- checkPat' p S.empty
  return (p', vs)
checkPat' :: UPat -> Set Ident -> Naming (UPat, Set Ident, [(Ident, Ident)])
checkPat' (PBinding () x) seen = do
  mX' <- tryLookup x
  case mX' of
    Just (NameEntry _ NKCons) -> return $ (PCons () x [], seen, [])
    _ -> do
      when (x `S.member` seen) $ throwError $ DuplicateNames [x]
      x' <- uniqId x
      return $ (PBinding () x', S.insert x seen, [(x, x')])
checkPat' p@(PCons () x ps) seen = do
   mK <- tryLookup x
   case mK of
     Just (NameEntry _ NKCons) -> do
       (ps', seen', vs) <-
         foldM (\(ps0, seen0, vs0) p -> do
                   (p', seen', vs') <- checkPat' p seen0
                   return (p':ps0, seen', vs0 ++ vs'))
            ([], seen, [])
            (reverse ps)
       return $ (PCons () x ps', seen', vs)
     _ ->
       -- A undefined nilary constructor? It's actually a binding!
       if null ps
       then do
         when (x `S.member` seen) $ throwError $ DuplicateNames [x]
         x' <- uniqId x
         return $ (PBinding () x', S.insert x seen, [(x, x')])
       else throwError $ InvalidPattern p
checkPat' p seen = return (p, seen, [])

checkCase :: UCase -> Naming UCase
checkCase (Case p _ e) = do
  (p', vs) <- checkPat p
  e' <- withVars vs $ checkExpr e
  return (Case p' (map (\(_, v) -> (v, ())) vs) e')

checkExpr :: UExpr -> Naming UExpr
checkExpr e =
  case e of
    EIdent () x  -> do
      ne <- lookup x
      curDepth <- nstDepth <$> get
      addDeps $ neName ne
      case neKind ne of
        NKLocal d | d /= curDepth -> throwError $ InvalidCapture (neName ne)
        NKLocal _ -> return $ ELocal () (neName ne)
        NKGlobal  -> return $ EGlobal () (neName ne)
        NKCons    -> return $ ECons () (neName ne)
    EApp () f xs -> (EApp ()) <$> (checkExpr f) <*> (mapM checkExpr xs)
    ELet () bs e -> checkLocals bs e
    EIf () e0 e1 e2 -> do
       e0' <- checkExpr e0
       e1' <- checkExpr e1
       e2' <- checkExpr e2
       return $ EIf () e0' e1' e2'
    ECase () e cs -> do
      e' <- checkExpr e
      cs' <- mapM checkCase cs
      return $ ECase () e' cs'
    _ -> return e

checkFunction :: Ident -> [Ident] -> UExpr -> Naming UFunction
checkFunction f xs e = do
  oldDepth <- nstDepth <$> get
  modify (\s -> s { nstDepth = oldDepth + 1 })
  (xs', (body, deps)) <- scopedVars' xs $ block (checkExpr e)
  modify (\s -> s { nstDepth = oldDepth })
  return $ Function f (MonoType ()) (map (\x -> (x, ())) xs') deps body

checkImplicitMain :: UExpr -> Naming UFunction
checkImplicitMain e = checkFunction (mkId "__fy_main") [] e

checkType :: Type -> Naming ()
checkType (TVar _) = error "Parametric types are not supported yet"
checkType (TCons x ts) = do
  t <- ((M.lookup x) . nstTypes) <$> get
  case t of
    Nothing -> throwError $ UndefinedType x
    Just _ -> mapM_ checkType ts
checkType (TFun ts t) = (checkType t) >> (mapM_ checkType ts)

checkTypeDef :: TypeDef -> Naming ()
checkTypeDef (TypeDef _ (TBCType _)) = return ()
checkTypeDef (TypeDef x (TBConses cs)) = do
  mapM_ checkAndIntroCons cs
  where
    checkAndIntroCons (TypeCons c ts) = do
      mapM_ checkType ts
      modify (\s -> s { nstScope = M.insert c (NameEntry c NKCons) $ nstScope s })

checkTypeDefs :: [TypeDef] -> Naming ()
checkTypeDefs tds = do
  modify (\s -> s { nstTypes = M.fromList $ builtins ++ (map (\td -> (tdName td, Just $ tdBody td)) tds) } )
  mapM_ checkTypeDef tds
  where
    builtins = map (\x -> (mkId x, Nothing)) ["int", "()"]

checkProgram :: UProgram -> Naming UFunction
checkProgram (Program tds e) = do
  checkTypeDefs tds
  checkImplicitMain e

namingCheck :: UProgram -> Either NamingError UFunction
namingCheck p = runNaming M.empty (checkProgram p)
