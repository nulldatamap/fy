{-# OPTIONS_GHC -Wno-orphans #-}
module Fy.Pretty () where

import Fy.Types
import Fy.Ast
import Fy.Ir

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
    align $ sep $ [(hsep $ (pretty n):argsDoc) `prettyTypeAnn` t]
                    ++ prettyDeps deps
                    ++ [nst $ sep ["=", pretty b]]
    where
      argsDoc :: [Doc a]
      argsDoc =
        if null args
        then ["()"]
        else map (pretty . fst) args

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


block :: [Doc a] -> Doc a
block ds = (nst $ vsep $ "{":ds) <> line <> "}" <> line

braced :: [Doc a] -> Doc a
braced = encloseSep lbrace rbrace comma

instance Pretty IRRecord where
  pretty (IRRecord n fs) = (pretty n) <+> (braced $ map (\(t, x ) -> (pretty x) <+> ":" <+> (pretty t)) fs)

instance Pretty IRTypeBody where
  pretty (IREnumType es) = "enum" <+> (braced $ map pretty es)
  pretty (IRStructType r) = "struct" <+> (pretty r)
  pretty (IRTaggedType rs) = align $ vsep $ map (\r -> "tag" <+> (pretty r)) rs
  pretty (IRCType c) = "ctype" <+> (pretty c)
  pretty (IRFunType t ts) = "fptr" <+> (tupled $ map pretty ts) <+> "->" <+> (pretty t)
  pretty (IRTypeAlias t) = "alias" <+> (pretty t)

instance Pretty IRTypeDef where
  pretty (IRTypeDef n rg isBoxed b) =
    hsep $ [ if isBoxed then "ref-type" else "val-type"
           , pretty n, braced $ map pretty $ S.toList rg, hng $ hsep ["=", pretty b] ]

instance Pretty Operator where
  pretty OpAdd = "+"
  pretty OpEq = "=="
  pretty OpAnd = "&&"

instance Pretty IRLit where
  pretty (IRInt i) = pretty i
  pretty IRVoid = "()"

instance Pretty IRExpr where
  pretty (IRVar x) = pretty x
  pretty (IROp o es) = (pretty o) <> (tupled $ map pretty es)
  pretty (IRCall x es) = (pretty x) <> (tupled $ map pretty es)
  pretty (IRCons t x es) = (pretty t) <> "/" <> (pretty x) <> (tupled $ map pretty es)
  pretty (IRLit l) = pretty l
  pretty (IRField e x) = (pretty e) <> "." <> (pretty x)
  pretty (IRCheckVariant e x y) = (pretty x) <> "/" <> (pretty y) <> "?" <+> (pretty e)

instance Pretty IRStmt where
  pretty (IRDef t n mX) = hsep $ ["var", pretty n, ":", pretty t] ++ xDoc
    where
      xDoc =
        case mX of
          Nothing -> []
          Just x -> ["=" <+> (pretty x)]
  pretty (IRSet x e) = hsep $ [pretty x, "<-", pretty e]
  pretty (IREval e) = pretty e
  pretty (IRReturn e) = hsep $ ["return", pretty e]
  pretty (IRIf e0 st0 [th@(IRIf _ _ _)]) =
    hsep $ [ "if", pretty e0
           , block $ map pretty st0
           , "else", pretty th ]
  pretty (IRIf e st0 st1) = hsep $ [ "if", pretty e
                                   , block $ map pretty st0
                                   , "else", block $ map pretty st1 ]
  pretty (IRPanic x) = hsep $ ["panic", enclose "\"" "\"" $ pretty x]


instance Pretty IRFunc where
  pretty (IRFunc n _ ret args b) =
    "func" <+> (pretty n) <> argsDoc <+> "->" <+> (pretty ret) <+> (block $ map pretty b)
     where
       argsDoc = tupled $ map (\(x, t) -> (pretty x) <+> ":" <+> (pretty t)) args

instance Pretty IRType where
  pretty (IRType t) = pretty t

instance Pretty IRVarDecl where
  pretty (IRVarDecl n _ t) = "var" <+> (pretty n) <+> ":" <+> (pretty t)

instance Pretty IRProgram where
  pretty (IRProgram n tys fns vs init) =
    "module" <+> (pretty n) <> line
      <> line <> (vsep $ map pretty tys) <> line
      <> line <> (vsep $ map pretty vs) <> line
      <> line <> ("init" <+> (block $ map pretty init)) <> line
      <> line <> (vsep $ map pretty fns)
