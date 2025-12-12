module Fy.Types
     ( FreeVars(..), Substitutable(..), Typed(..), Env, Subst(..)
     , TyVar, Ident(..), Type(..), TypeSchemeT(..), TypeScheme
     , Context(..)
     , mkId, suffixId, canonicalId, enumeratedIds
     , unnamedFields, variantField, typeName
     , builtinTypeNames, isBuiltinType
     , encodeType, unFn, isFnTy, tUnit, tInt, tBool
     ) where


import Prelude hiding (lookup, lines)
import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Hashable (Hashable)
import Data.Set (Set)
import qualified Data.Set as S
import Data.List (intercalate, elemIndex)
import Data.Maybe (fromMaybe)
import Control.Monad.Except
import qualified Data.HashMap.Strict as M
import Prettyprinter

data Ident = Ident { idName :: Text
                   , idNamespace :: [Text]
                   , idSuffix :: (Maybe Int) }
  deriving (Ord, Eq, Generic)

deriving instance Hashable Ident

type TyVar = Int

data Type = TVar TyVar
          | TCons Ident [Type]
          | TFun [Type] Type
          deriving (Eq, Generic)

deriving instance Hashable Type

data TypeSchemeT t = MonoType t
                  | PolyType [TyVar] t
                  deriving (Eq, Functor, Foldable)

type TypeScheme = TypeSchemeT Type

data Subst = Subst (M.HashMap Int Type)
  deriving (Show)

type Env = M.HashMap Ident TypeScheme

class Functor a => Typed a where
  withType :: (Type -> a Type -> x) -> a Type -> x
  typeOf :: (a Type) -> Type
  typeOf = withType (\t _ -> t)

class FreeVars a where
  freeVars :: a -> Set TyVar

class Substitutable a where
  subst :: Subst -> a -> a

instance Show Ident where
  show (Ident n ns sf) =
    (intercalate "/" $ map T.unpack $ ns ++ [n])
    ++ (fromMaybe "" $ fmap (('$':) . show) sf)

class (Hashable k, Monad m, MonadError e m) => Context m k v e
    | m -> e, m -> k, m -> v where

  getContext :: m (M.HashMap k v)
  modifyContext :: (M.HashMap k v -> M.HashMap k v) -> m ()
  undefinedVar :: k -> m a

  tryLookup :: k -> m (Maybe v)
  tryLookup k = (M.lookup k) <$> getContext

  lookup :: k -> m v
  lookup k = do
    v <- tryLookup k
    case v of
      Nothing -> undefinedVar k
      Just x -> return x

  insert :: k -> v -> m ()
  insert k v = modifyContext (M.insert k v)

  scoped :: [(k, v)] -> m a -> m a
  scoped kvs m = do
    oldCtx <- getContext
    mapM_  (uncurry insert) kvs
    r <- m
    modifyContext (const oldCtx)
    return r

instance FreeVars Type where
    freeVars (TVar x) = S.singleton x
    freeVars (TCons _ ts) = foldMap freeVars ts
    freeVars (TFun ts t) = (foldMap freeVars ts) `S.union` (freeVars t)

instance FreeVars TypeScheme where
  freeVars (MonoType t) = freeVars t
  freeVars (PolyType ts t) = (freeVars t) S.\\ (S.fromList $ ts)

instance FreeVars Env where
  freeVars env = M.foldl' (\vs x -> vs `S.union` (freeVars x)) S.empty env

instance Substitutable Type where
    subst (Subst m) (TVar x) = fromMaybe (TVar x) $ M.lookup x m
    subst s (TCons k ts) = TCons k $ map (subst s) ts
    subst s (TFun ts t)  = TFun (map (subst s) ts) (subst s t)

instance Substitutable TypeScheme where
  subst s (MonoType t) = MonoType $ subst s t
  -- ASSUMPTION: All the type variables are fresh and shouldn't exist in s
  subst s (PolyType ts t) = PolyType ts $ subst s t

instance Show Type where
  show (TVar x) = "'t" ++ show x
  show (TCons x []) = show x
  show (TCons x ts) = "(" ++ (intercalate " " $ (show x) : (map show ts)) ++  ")"
  show (TFun ts t) = "(" ++ (intercalate ", " $ map show ts) ++ " -> " ++ (show t) ++ ")"

instance Show a => Show (TypeSchemeT a)  where
  show (MonoType t) = show t
  show (PolyType ts t) = "forall " ++ (intercalate " " $ map (show . TVar) ts) ++ " . " ++ (show t)

instance Semigroup Ident where
  (<>) (Ident a aNs Nothing) (Ident b bNs bI) = Ident b (aNs ++ [a] ++ bNs) bI
  (<>) a b = error $ "Can't combine the idents: `" ++ (show a) ++ "` and `" ++  (show b) ++ "`"

mkId :: Text -> Ident
mkId x = Ident x [] Nothing

suffixId :: Ident -> Text -> Ident
suffixId (Ident x ns i) s = Ident (T.append x s) ns i

canonicalId :: Ident -> Text
canonicalId (Ident n mNs mI) = T.concat $ prefix ++ (n : suffix)
  where
    prefix = concat $ fmap (\ns -> [ns, "_"]) mNs
    suffix = fromMaybe [] $ fmap (\i -> ["_", T.pack $ show i]) mI

enumeratedIds :: Text -> [Ident]
enumeratedIds s = map (\i -> Ident s [] (Just i)) [0..]

unnamedFields :: [Ident]
unnamedFields = enumeratedIds ""

variantField :: Ident
variantField = mkId "__variant"

typeName :: Type -> Ident
typeName (TVar i) = Ident "'t" [] (Just i)
typeName (TCons c _) = c
typeName (TFun xs _) = mkId $ T.pack $ replicate (length xs) ',' ++ "->"

tInt :: Type
tInt = TCons (mkId "int") []

tBool :: Type
tBool = TCons (mkId "bool") []

tUnit :: Type
tUnit = TCons (mkId "()") []

builtinTypeNames :: [Text]
builtinTypeNames = ["int", "bool", "9"]

isBuiltinType :: Type -> Bool
isBuiltinType (TCons (Ident x [] Nothing) []) = x `elem` builtinTypeNames
isBuiltinType _ = False

unFn :: Type -> Maybe ([Type], Type)
unFn (TFun ts t) = Just (ts, t)
unFn _ = Nothing

isFnTy :: Type -> Bool
isFnTy (TFun _ _) = True
isFnTy _          = False

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
        Nothing -> error $ "Tried to encode a type with a free variable: " ++ (show t)
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
