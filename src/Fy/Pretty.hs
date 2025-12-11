{-# OPTIONS_GHC -Wno-orphans #-}
module Fy.Pretty () where

import Fy.Types
import Fy.Ast

import Data.Set (Set)
import qualified Data.Set as S
import Prettyprinter

instance Pretty Lit where
  pretty (LInt i) = pretty i
  pretty LUnit = "()"

class Pretty a => TypeAnn a where
  prettyTypeAnn :: Doc b -> a -> Doc b

instance TypeAnn () where
  prettyTypeAnn x _ = x

instance TypeAnn Type where
  prettyTypeAnn x t = x <+> ":" <+> (pretty t)

instance (Show a, Pretty a) => TypeAnn (TypeSchemeT a) where
  prettyTypeAnn x (MonoType t) = x <+> ":" <+> (pretty t)
  prettyTypeAnn x (PolyType ts t) =
    x <+> ":" <+> ("forall" <+> (hsep $ map (pretty . TVar) ts) <+> "." <+> pretty t)

instance Pretty Builtin where
  pretty BAdd = "$$add"
  pretty BEq = "$$eq"

nst :: Doc a -> Doc a
nst = nest 2

hng :: Doc a -> Doc a
hng = hang 2

prettyDeps :: Set Ident -> [Doc a]
prettyDeps deps =
  if S.null deps
  then []
  else [enclose "{" "}" $ go $ S.toList deps]
  where
    go :: [Ident] -> Doc a
    go [] = emptyDoc
    go [x] = pretty x
    go (x0:x1:xs) = (pretty x0) <> "," <> (go $ x1:xs)

instance (Show t, TypeAnn t) => Pretty (Binding t) where
  pretty (Binding t n pub deps b) =
    case b of
      Val e -> "." <+> (align $ sep $ [pretty n]
                                        ++ prettyDeps deps
                                        ++ [nst $ sep ["=", pretty e]])
      Fun f -> "." <+> pretty f

instance (Show t, TypeAnn t) => Pretty (Function t) where
  pretty (Function n t args pub deps b) =
    align $ sep $ [(hsep $ map pretty $ n:(map fst args)) `prettyTypeAnn` t]
                    ++ prettyDeps deps
                    ++ [nst $ sep ["=", pretty b]]

instance (Show t, TypeAnn t) => Pretty (Pat t) where
  pretty (PHole t) = "_" `prettyTypeAnn` t
  pretty (PLit t l) = (pretty l) `prettyTypeAnn` t
  pretty (PBinding t x) = (pretty x) `prettyTypeAnn` t
  pretty (PCons t x ps) = (parens $ hsep $ (pretty x) : (map pretty ps)) `prettyTypeAnn` t

instance (Show t, TypeAnn t) => Pretty (Case t) where
  pretty (Case p bs arm) = "|" <+> (hng $ sep $ [pretty p]
                                                  ++ bsDoc
                                                  ++ [hng $ sep $ ["->", (pretty arm)]])
    where
        bsDoc =
            if null bs
            then []
            else [enclose "{" "}" $ go bs]
        binding (x, t) = (pretty x) <+> ":" <+> (pretty t)
        go [] = emptyDoc
        go [x] = binding x
        go (x0:x1:xs) = (binding x0) <> "," <> (go $ x1:xs)

instance (Show t, TypeAnn t) => Pretty (Expr t) where
  pretty (ELit t l) = (pretty l) `prettyTypeAnn` t
  pretty (ETup t es) = (tupled $ map pretty es) `prettyTypeAnn` t
  pretty (EBuiltin _ b) = pretty b
  pretty (EIdent t x) = (pretty x) `prettyTypeAnn` t
  pretty (EApp t e es) = (parens $ hng $ sep $ map (group . pretty) (e:es)) `prettyTypeAnn` t
  pretty (ELet t bs e) = parens $ align $ sep $ (pretty e) : (map pretty bs)
  pretty (EIf t e0 e1 e2) = align $ vsep [ "if" <+> (pretty e0)
                                         , "then" <+> (hng $ pretty e1)
                                         , "else" <+> (hng $ pretty e2) ] `prettyTypeAnn` t
  pretty (ECase t e0 cs) = (align $ sep $ (pretty e0):(map pretty cs)) `prettyTypeAnn` t
  pretty (ELocal t x) = (pretty x) `prettyTypeAnn` t
  pretty (EGlobal t x) = ("/" <> (pretty x)) `prettyTypeAnn` t
  pretty (ECons t x) = parens $ (pretty x) `prettyTypeAnn` t

instance Pretty PathItem where
  pretty (PathItem ps h alias) = hsep $ path : al
    where
      al =
        case alias of
          Nothing -> []
          Just x -> ["=" <+> (pretty x)]
      path :: Doc b
      path = go ps h ""
      go (p0:p1:ps') h r = go (p1:ps') h (r <> (pretty p0) <> "/")
      go (p:ps') h r = go ps' h (r <> (pretty p))
      go [] Nothing r = r
      go [] (Just Nothing) r = r <> "/*"
      go [] (Just (Just ns)) r = r <> "/" <> (tupled $ map pretty ns)

instance Pretty TypeCons where
  pretty (TypeCons n ms) = "|" <+> (hng $ sep $ (pretty n):(map pretty ms))

instance Pretty TypeBody where
  pretty (TBConses cs) = align $ vsep $ map pretty cs
  pretty (TBCType c) = "$$ctype" <+> (pretty c)
  pretty (TBAlias n) = pretty n

instance Pretty TypeDef where
  pretty (TypeDef n prs b) =
    ":" <+> (sep $ (pretty n):(map pretty prs) ++ [align $ sep ["=", pretty b]])

instance (Show t, TypeAnn t) => Pretty (Module t) where
  pretty (Module n im ex ts is) =
    vsep $ (pretty n) : (exDoc ++ imDoc ++ (map pretty ts) ++ (map pretty is))
    where
      imDoc = map (\x -> "<-" <+> (pretty x)) im
      exDoc = map (\x -> "->" <+> (pretty x)) ex
