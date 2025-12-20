module Fy.Ast
  ( TypeCons(..), TypeDef(..), TypeBody(..)
  , Program(..), Builtin(..), ValOrFun(..)
  , Binding(..), Function(..), Lit(..)
  , Case(..), Expr(..), Pat(..)
  , Module(..), PathItem(..), Publicity(..)
  , UModule, UProgram, UPat, UCase, UExpr, UFunction, UBinding
  , TModule, TProgram, TPat, TCase, TExpr, TFunction, TBinding
  , AstVisitor(..), newVisitor, visitFunction, visitBinding, visitExpr, visitCase, visitPat
  , isFun, bindingFromFunction, TypeDeps(..)
  ) where


import Fy.Types

import Prelude hiding (lookup, lines)
import Data.Text (Text)
import Data.Set (Set)
import qualified Data.Set as S

data Publicity = Private
               | Public
               | CExport Text
               deriving (Show, Eq)

data PathItem = PathItem { piPath  :: [Text]
                         , piHead  :: Maybe (Maybe [Ident])
                         , piAlias :: Maybe Ident }
  deriving (Show)

data Module t = Module { mName :: Ident
                       , mImports :: [PathItem]
                       , mExports :: [PathItem]
                       , mTypeDefs :: [TypeDef]
                       , mItems :: [Binding t] }
  deriving (Show)

data TypeCons = TypeCons { tdcName :: Ident, tdcMembers :: [Type] }
  deriving (Show)

data TypeBody = TBConses [TypeCons]
              | TBCType Text
              | TBAlias Type
  deriving (Show)

data TypeDef = TypeDef { tdName :: Ident
                       , tdParams :: [Type]
                       , tdRecursionGroup :: Set Ident
                       , tdBody :: TypeBody }
  deriving (Show)

data Program t = Program { pTypeDefs :: [TypeDef], pBody :: (Expr t) }
  deriving (Show)

data Builtin = BAdd
             | BEq
    deriving Show

data ValOrFun t = Val (Expr t) | Fun (Function t)
  deriving (Show, Functor, Foldable)

data Binding t = Binding { bType :: TypeSchemeT t
                         , bName :: Ident
                         , bPub  :: Publicity
                         , bDeps :: Set Ident
                         , bBody :: ValOrFun t }
  deriving (Show, Foldable, Functor)

data Function t = Function { fName   :: Ident
                           , fType   :: TypeSchemeT t
                           , fArgs   :: [(Ident, t)]
                           , fEnv    :: [(Ident, t, Expr t)]
                           , fPub    :: Publicity
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
            | ELet t [Binding t] (Expr t)
            | EIf t (Expr t) (Expr t) (Expr t)
            | ECase t (Expr t) [Case t]
            | ELam t [(Ident, t)] (Set Ident) [(Ident, t, Expr t)] (Expr t)
            -- Never parsed:
            | ELocal t Ident
            | ECapture t Ident
            | EGlobal t Ident
            | ECons t Ident
    deriving (Show, Functor, Foldable)

type UModule   = Module ()
type UProgram  = Program ()
type UPat      = Pat ()
type UCase     = Case ()
type UExpr     = Expr ()
type UFunction = Function ()
type UBinding  = Binding ()

type TModule   = Module Type
type TProgram  = Program Type
type TPat      = Pat Type
type TCase     = Case Type
type TExpr     = Expr Type
type TFunction = Function Type
type TBinding  = Binding Type

instance Typed Expr where
  withType f x@(ELit t _) = f t x
  withType f x@(EIdent t _) = f t x
  withType f x@(ELocal t _) = f t x
  withType f x@(ECapture t _) = f t x
  withType f x@(EGlobal t _) = f t x
  withType f x@(ECons t _) = f t x
  withType f x@(EBuiltin t _) = f t x
  withType f x@(EApp t _ _) = f t x
  withType f x@(ELet t _ _) = f t x
  withType f x@(ELam t _ _ _ _) = f t x
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

instance Substitutable (Binding Type) where
  subst s l = l { bType = subst s $ bType l
                , bBody = subst s $ bBody l }

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
  subst s (TypeDef n ps rg b) = TypeDef n (map (subst s) ps) rg $ subst s b

instance Substitutable (Module Type) where
  subst s m@(Module { mItems = bs }) =
    m { mItems = map (subst s) bs }

class TypeDeps a where
  typeDeps :: a -> Set Ident

instance TypeDeps Type where
  typeDeps (TFun ts t) = S.union (typeDeps t) $ S.unions $ map typeDeps ts
  typeDeps (TCons c ts) = S.insert c $ S.unions $ map typeDeps ts
  typeDeps _ = S.empty

instance TypeDeps TypeCons where
  typeDeps (TypeCons _ ts) = S.unions $ map typeDeps ts

instance TypeDeps TypeBody where
  typeDeps (TBConses cs) = S.unions $ map typeDeps cs
  typeDeps (TBAlias t) = typeDeps t
  typeDeps _ = S.empty

instance TypeDeps TypeDef where
  typeDeps (TypeDef _ _ _ b) = typeDeps b

data AstVisitor m t =
  AstVisitor { avPreFunction :: Function t -> m (Function t)
             , avPostFunction :: Function t -> m (Function t)
             , avPreBinding :: Binding t -> m (Binding t)
             , avPostBinding :: Binding t -> m (Binding t)
             , avPreExpr  :: Expr t -> m (Expr t)
             , avPostExpr :: Expr t -> m (Expr t)
             , avPreCase :: Case t -> m (Case t)
             , avPostCase :: Case t -> m (Case t)
             , avPrePat :: Pat t -> m (Pat t)
             , avPostPat :: Pat t -> m (Pat t) }

newVisitor :: Monad m => AstVisitor m t
-- Oh dear dear:
newVisitor = AstVisitor -- I miss you already
  -- I hope you will soon:
  return
  return
  return
  return
  return
  return
  return
  return
  return
  return

visitFunction :: Monad m => AstVisitor m t -> Function t -> m (Function t)
visitFunction v f = do
  f' <- avPreFunction v f
  body' <- visitExpr v $ fBody f'
  avPostFunction v $ f' { fBody = body' }

visitBinding :: Monad m => AstVisitor m t -> Binding t -> m (Binding t)
visitBinding v b = do
  b' <- avPreBinding v b
  body' <- case bBody b' of
             Val e -> Val <$> (visitExpr v e)
             Fun f -> Fun <$> (visitFunction v f)
  avPostBinding v $ b' { bBody = body' }

visitExpr :: Monad m => AstVisitor m t -> Expr t -> m (Expr t)
visitExpr v e = do
  e' <- avPreExpr v e
  e'' <- case e' of
           ETup t es -> (ETup t) <$> (mapM recur es)
           EApp t e0 es -> (EApp t) <$> (recur e0) <*> (mapM recur es)
           ELet t bs e0 -> (ELet t) <$> (mapM (visitBinding v) bs) <*> (recur e0)
           EIf t e0 e1 e2 -> (EIf t) <$> (recur e0) <*> (recur e1) <*> (recur e2)
           ECase t e0 cs -> (ECase t) <$> (recur e0) <*> (mapM (visitCase v) cs)
           ELam t xs deps caps e0 -> (ELam t xs deps caps) <$> (recur e0)
           _ -> return e
  avPostExpr v e''
  where
    recur = visitExpr v

visitCase :: Monad m => AstVisitor m t -> Case t -> m (Case t)
visitCase v c = do
  c' <- avPreCase v c
  p' <- visitPat v $ cPat c'
  e' <- visitExpr v $ cArm c'
  avPostCase v $ c' { cPat = p', cArm = e' }

visitPat :: Monad m => AstVisitor m t -> Pat t -> m (Pat t)
visitPat v p = do
  p' <- avPrePat v p
  p'' <- case p' of
           PCons t x ps -> (PCons t x) <$> (mapM (visitPat v) ps)
           _ -> return p'
  avPostPat v p''

bindingFromFunction :: Function a -> Binding a
bindingFromFunction f@(Function n t _ _ p d _) = Binding t n p d (Fun f)

isFun :: ValOrFun t -> Bool
isFun (Fun _) = True
isFun _       = False
