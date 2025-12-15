module Fy.Naming
  ( namingCheck
  ) where


import Fy.Types
import Fy.Ast

import Prelude hiding (lookup, lines)
import qualified Data.Set as S
import Data.List (elemIndex, unsnoc)
import Data.Set (Set)
import Control.Monad (when, unless, foldM)
import Control.Monad.State
import Control.Monad.Except
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

data NamingSt = NamingSt { nstNext    :: Int
                         , nstDepth   :: Int
                         , nstDeps    :: Set Ident
                         , nstTypes   :: TypeDefMap
                         , nstExports :: Set Ident
                         , nstScope   :: NameMap }

data NamingError = UndefinedName Ident
                 | UndefinedType Ident
                 | InvalidCapture Ident
                 | DuplicateNames [Ident]
                 | InvalidPattern UPat
                 | UnresolvedExports [Ident]
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

removeDeps :: [Ident] -> Naming ()
removeDeps xs =
    modify (\s -> s { nstDeps = (nstDeps s) S.\\ (S.fromList xs) })

runNaming :: NameMap -> Naming a -> Either NamingError a
runNaming gs n = runExcept (evalStateT n st)
  where
    st = NamingSt { nstNext = 0
                  , nstScope = gs
                  , nstDepth = 0
                  , nstExports = S.empty
                  , nstDeps = S.empty
                  , nstTypes = M.empty }

withVars :: [(Ident, Ident)] -> Naming a -> Naming a
withVars xs m = do
    d <- nstDepth <$> get
    r <- scoped (map (\(x, x') -> (x, NameEntry x' (NKLocal d))) xs) m
    removeDeps $ map snd xs
    return r

scopedVars' :: [Ident] -> Naming a -> Naming ([Ident], a)
scopedVars' xs m = do
    d <- nstDepth <$> get
    let isGlobal = d == 0
    (_, xs') <- foldM (\(seen, xs') x -> do
                          if x `S.member` seen
                          then throwError $ DuplicateNames [x]
                          else do
                            x' <- if isGlobal then return x else uniqId x
                            return (S.insert x seen, x':xs')) (S.empty, []) $ reverse xs
    let nk = if isGlobal then NKGlobal else (NKLocal d)
    r <- scoped (map (\(x, x') -> (x, NameEntry x' nk)) $ zip xs xs') $ ((,) xs') <$> m
    removeDeps xs'
    return r

scopedVars :: [Ident] -> Naming a -> Naming a
scopedVars xs m = snd <$> scopedVars' xs m

checkLocals :: [UBinding] -> UExpr -> Naming UExpr
checkLocals ls e = do
  (ls', e') <- scopedVars (map (\(Binding { bName = x }) -> x) ls) $ do
    ls' <- mapM checkBinding ls
    e' <- checkExpr e
    return (ls', e')
  return $ ELet () ls' e'

checkBindings :: [UBinding] -> Naming [UBinding]
checkBindings ls = do
  scopedVars (map bName ls) $ mapM checkBinding ls

checkExported :: Ident -> Naming Publicity
checkExported x = do
  exports <- nstExports <$> get
  if x `S.member` exports
  then do
    modify (\s -> s { nstExports = S.delete x exports })
    return $ Public
  else return Private

checkBinding :: UBinding -> Naming (Binding ())
checkBinding (Binding t x _ _ (Val e)) = do
  (NameEntry x' _) <- lookup x
  p <- checkExported x
  -- checkFunction always increments the depth, but the value equivalent
  -- Does not (because we don't want to increase the depth through let-bindings)
  -- But specifically in the case of top-level value bindings we need to increase
  -- the depth, so that nested let-bindings aren't treated at globals
  d <- nstDepth <$> get
  modify (\s -> s { nstDepth = d + 1 })
  (e', deps) <- block $ checkExpr e
  modify (\s -> s { nstDepth = d })
  return $ Binding t x' p deps (Val e')
checkBinding (Binding t x _ _ (Fun f)) = do
   (NameEntry x' _) <- lookup x
   p <- checkExported x
   f' <- checkFunction x' (map fst $ fArgs f) p (fBody f)
   return $ Binding t x' p (fDeps f') (Fun f')

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
checkPat' p0@(PCons () x ps) seen = do
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
       else throwError $ InvalidPattern p0
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
    ELet () bs e0 -> checkLocals bs e0
    EIf () e0 e1 e2 -> do
       e0' <- checkExpr e0
       e1' <- checkExpr e1
       e2' <- checkExpr e2
       return $ EIf () e0' e1' e2'
    ECase () e0 cs -> do
      e0' <- checkExpr e0
      cs' <- mapM checkCase cs
      return $ ECase () e0' cs'
    ELam () xs e0 -> error "TODO: checkExpr ELam"
    _ -> return e

checkFunction :: Ident -> [Ident] -> Publicity -> UExpr -> Naming UFunction
checkFunction f xs p e = do
  oldDepth <- nstDepth <$> get
  modify (\s -> s { nstDepth = oldDepth + 1 })
  ((xs', body), deps) <- block $ scopedVars' xs $ checkExpr e
  modify (\s -> s { nstDepth = oldDepth })
  return $ Function f (MonoType ()) (map (\x -> (x, ())) xs') p deps body

checkType :: [Ident] -> Type -> Naming Type
checkType _ (TVar _) = error "Parametric types are not supported yet"
checkType ps (TCons x ts) = do
  types <- nstTypes <$> get
  case elemIndex x ps of
    Nothing | not $ M.member x types -> throwError $ UndefinedType x
    Just t | null ts -> return $ TVar t
    Just _ -> error "Can't use a type-variable as a constructor"
    _ -> (TCons x) <$> mapM (checkType ps) ts
checkType ps (TFun ts t) = TFun <$> (mapM (checkType ps) ts) <*> (checkType ps t)

checkTypeDef :: TypeDef -> Naming TypeDef
checkTypeDef td = do
  _ <- checkExported (tdName td)
  checkTypeDef' td

checkTypeDef' :: TypeDef -> Naming TypeDef
checkTypeDef' td@(TypeDef _ _ _ (TBCType _)) = return td
checkTypeDef' td@(TypeDef _ _ _ (TBAlias t)) = do
  t' <- checkType [] t
  return $ td { tdBody = TBAlias t' }
checkTypeDef' (TypeDef tn tPrms rg (TBConses cs)) = do
  cs' <- mapM checkAndIntroCons cs
  return $ TypeDef tn (take (length tPrms) $ map TVar [0 :: Int ..]) rg (TBConses cs')
  where
    ps = map (\pt ->
                  case pt of
                    TCons ct [] -> ct
                    _ -> error $ "Type definition paramter was not a variable: " ++ (show pt))
           tPrms
    checkAndIntroCons (TypeCons c ts) = do
      ts' <- mapM (checkType ps) ts
      let qn = tn <> c
      modify (\s -> s { nstScope = M.insert qn (NameEntry qn NKCons) $ nstScope s })
      return $ TypeCons (tn <> c) ts'

checkTypeDefs :: [TypeDef] -> Naming [TypeDef]
checkTypeDefs tds = do
  types <-
      foldM (\m (TypeDef tn _ _ tb) ->
               if tn `M.member` m
               then throwError $ DuplicateNames [tn]
               else return $ M.insert tn (Just tb) m)
        builtins
        tds
  modify (\s -> s { nstTypes =  types} )
  mapM checkTypeDef tds
  where
    builtins = M.fromList $ map (\x -> (mkId x, Nothing)) ["int", "()"]

registerExport :: PathItem -> Naming ()
registerExport (PathItem ps Nothing Nothing) =
  let (ns, n) = case unsnoc ps of
                  Nothing -> error $ "Empty path item??"
                  Just x -> x
  in modify (\s -> s { nstExports = S.insert (Ident n ns Nothing) $ nstExports s })
registerExport p = error $ "Unsupported export: " ++ (show p)

checkModule :: UModule -> Naming UModule
checkModule m = do
  mapM_ registerExport $ mExports m
  tds' <- checkTypeDefs $ mTypeDefs m
  is <- checkBindings $ mItems m
  exs <- nstExports <$> get
  unless (null exs) $ throwError $ UnresolvedExports $ S.toList exs
  return m { mTypeDefs = tds', mItems = is }

namingCheck :: UModule -> Either NamingError UModule
namingCheck m = runNaming M.empty (checkModule m)
