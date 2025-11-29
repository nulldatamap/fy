module Fy.Types
     ( FreeVars(..), Substitutable(..), Typed(..), Env(..), Subst(..)
     , TyVar(..), Ident(..), Type(..), TypeSchemeT(..), TypeScheme(..)
     , Context(..)
     , mkId, suffixId, canonicalId, enumeratedIds
     , unnamedFields, variantField, variant, typeName
     , unFn, isFnTy, tUnit, tInt, tBool
     ) where

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

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

data Ident = Ident { idName :: Text
                   , idNamespace :: (Maybe Text)
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
    (fromMaybe "" $ fmap ((++"/") . T.unpack) ns)
    ++ (T.unpack n)
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

instance Show Type where
  show (TVar x) = "'t" ++ show x
  show (TCons x []) = show x
  show (TCons x ts) = "(" ++ (show x) ++ (intercalate " " $ map show ts) ++  ")"
  show (TFun ts t) = "(" ++ (intercalate ", " $ map show ts) ++ " -> " ++ (show t) ++ ")"

instance Show a => Show (TypeSchemeT a)  where
  show (MonoType t) = show t
  show (PolyType ts t) = "forall " ++ (intercalate " " $ map (show . TVar) ts) ++ " . " ++ (show t)

mkId :: Text -> Ident
mkId x = Ident x Nothing Nothing

suffixId :: Ident -> Text -> Ident
suffixId (Ident x ns i) s = Ident (T.append x s) ns i
canonicalId :: Ident -> Text
canonicalId (Ident n ns id) = T.concat $ prefix ++ (n : suffix)
  where
    prefix = fromMaybe [] $ fmap (\ns -> ["__", ns, "_"]) ns
    suffix = fromMaybe [] $ fmap (\id -> ["_", T.pack $ show id]) id

enumeratedIds :: Text -> [Ident]
enumeratedIds s = map (\i -> Ident s Nothing (Just i)) [0..]

unnamedFields :: [Ident]
unnamedFields = enumeratedIds ""

variantField :: Ident
variantField = mkId "__variant"

variant :: Ident -> Ident -> Ident
variant t x = Ident (canonicalId x) (Just $ canonicalId t) Nothing

typeName :: Type -> Ident
typeName (TVar i) = Ident "'t" Nothing (Just i)
typeName (TCons c _) = c
typeName (TFun xs _) = mkId $ T.pack $ replicate (length xs) ',' ++ "->"

tInt :: Type
tInt = TCons (mkId "int") []

tBool :: Type
tBool = TCons (mkId "bool") []

tUnit :: Type
tUnit = TCons (mkId "()") []

unFn :: Type -> Maybe ([Type], Type)
unFn (TFun ts t) = Just (ts, t)
unFn _ = Nothing

isFnTy :: Type -> Bool
isFnTy (TFun _ _) = True
isFnTy _          = False
