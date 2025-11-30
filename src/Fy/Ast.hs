module Fy.Ast
  ( TypeCons(..), TypeDef(..), TypeBody(..)
  , Program(..), Builtin(..), ValOrFun(..)
  , Local(..), Function(..), Lit(..)
  , Case(..), Expr(..), Pat(..)
  , UProgram, UPat, UCase, UExpr, UFunction
  , TProgram, TPat, TCase, TExpr, TFunction
  , isFun
  ) where


import Fy.Types

import Prelude hiding (lookup, lines)
import Data.Text (Text)
import Data.Set (Set)

data TypeCons = TypeCons { tdcName :: Ident, tdcMembers :: [Type] }
  deriving (Show)

data TypeBody = TBConses [TypeCons]
              | TBCType Text
  deriving (Show)

data TypeDef = TypeDef { tdName :: Ident
                       , tdParams :: [Type]
                       , tdBody :: TypeBody }
  deriving (Show)

data Program t = Program { pTypeDefs :: [TypeDef], pBody :: (Expr t) }
  deriving (Show)

data Builtin = BAdd
             | BEq
    deriving Show

data ValOrFun t = Val (Expr t) | Fun (Function t)
  deriving (Show, Functor, Foldable)

data Local t = Local { lType :: TypeSchemeT t
                     , lName :: Ident
                     , lDeps :: Set Ident
                     , lBody :: ValOrFun t }
  deriving (Show, Foldable, Functor)

data Function t = Function { fName   :: Ident
                           , fType   :: TypeSchemeT t
                           , fArgs   :: [(Ident, t)]
                           , fDeps   :: Set Ident
                           , fBody   :: Expr t }
  deriving (Show, Foldable, Functor)


data Lit = LInt Integer
         | LUnit
         deriving Show

data Pat t = PHole t
           | PLit t Lit
           | PBinding t Ident
           | PCons t Ident [Pat t]
  deriving (Show, Functor, Foldable)

data Case t = Case { cPat :: Pat t
                   , cBindings :: [(Ident, t)]
                   , cArm :: Expr t }
  deriving (Show, Functor, Foldable)

data Expr t = ELit t Lit
            | ETup t [Expr t]
            | EBuiltin t Builtin
            | EIdent t Ident
            | EApp t (Expr t) [Expr t]
            | ELet t [Local t] (Expr t)
            | EIf t (Expr t) (Expr t) (Expr t)
            | ECase t (Expr t) [Case t]
            -- Never parsed:
            | ELocal t Ident
            -- | ECapture t Ident
            | EGlobal t Ident
            | ECons t Ident
    deriving (Show, Functor, Foldable)

type UProgram  = Program ()
type UPat      = Pat ()
type UCase     = Case ()
type UExpr     = Expr ()
type UFunction = Function ()

type TProgram  = Program Type
type TPat      = Pat Type
type TCase     = Case Type
type TExpr     = Expr Type
type TFunction = Function Type

instance Typed Expr where
  withType f x@(ELit t _) = f t x
  withType f x@(EIdent t _) = f t x
  withType f x@(ELocal t _) = f t x
  withType f x@(EGlobal t _) = f t x
  withType f x@(ECons t _) = f t x
  withType f x@(EBuiltin t _) = f t x
  withType f x@(EApp t _ _) = f t x
  withType f x@(ELet t _ _) = f t x
  withType f x@(EIf t _ _ _) = f t x
  withType f x@(ECase t _ _) = f t x
  withType f x@(ETup t _) = f t x

instance Typed Pat where
  withType f x@(PHole t) = f t x
  withType f x@(PLit t _) = f t x
  withType f x@(PBinding t _) = f t x
  withType f x@(PCons t _ _) = f t x

instance Substitutable (ValOrFun Type) where
  subst s (Val v) = Val $ subst s v
  subst s (Fun f) = Fun $ subst s f

instance Substitutable (Local Type) where
  subst s l = l { lType = subst s $ lType l
                , lBody = subst s $ lBody l }

instance Substitutable TFunction  where
  subst s f = f { fBody = subst s $ fBody f
                , fType = subst s $ fType f
                , fArgs = map (\(x, t) -> (x, subst s t)) $ fArgs f }

instance Substitutable (Expr Type) where
  subst s x = fmap (subst s) x

instance Substitutable TypeCons where
  subst s (TypeCons tn ms) = TypeCons tn $ map (subst s) ms

instance Substitutable TypeBody where
  subst s (TBConses cs) = TBConses $ map (subst s) cs
  subst _ x = x

instance Substitutable TypeDef where
  subst s (TypeDef n ps b) = TypeDef n (map (subst s) ps) $ subst s b

isFun :: ValOrFun t -> Bool
isFun (Fun _) = True
isFun _       = False
