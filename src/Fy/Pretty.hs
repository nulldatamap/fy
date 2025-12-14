{-# OPTIONS_GHC -Wno-orphans #-}
module Fy.Pretty
  ( CPretty(..)
  ) where

import Fy.Types
import Fy.Ast
import Fy.Ir

import Prelude hiding (init)
import Data.Text (Text)
import Data.Set (Set)
import qualified Data.Set as S
import Prettyprinter
import Prettyprinter.Render.Terminal


type CDoc = Doc AnsiStyle

class CPretty a where
  cpretty :: a -> CDoc

instance CPretty () where cpretty = pretty
instance CPretty Int where cpretty = pretty
instance CPretty Text where cpretty = pretty
instance CPretty Integer where cpretty = pretty

cdf :: CDoc -> CDoc
cdf = annotate $ color White

ckw :: CDoc -> CDoc
ckw = annotate $ color Blue

cig :: CDoc -> CDoc
cig = annotate $ color Black

cty :: CDoc -> CDoc
cty = annotate $ colorDull Cyan

ccn :: CDoc -> CDoc
ccn = annotate $ color Red

clc :: CDoc -> CDoc
clc = annotate $ color Blue

cgl :: CDoc -> CDoc
cgl = annotate $ color White

cbi :: CDoc -> CDoc
cbi = annotate $ color Yellow

clt :: CDoc -> CDoc
clt = annotate $ colorDull Magenta

instance CPretty Ident where
  cpretty = viaShow

instance CPretty Type where
  cpretty = viaShow

instance (Show a) => CPretty (TypeSchemeT a) where
  cpretty = viaShow

instance CPretty Lit where
  cpretty (LInt i) = clt $ cpretty i
  cpretty LUnit = clt "()"

class CPretty a => TypeAnn a where
  prettyTypeAnn :: CDoc -> a -> CDoc

instance TypeAnn () where
  prettyTypeAnn x _ = x

instance TypeAnn Type where
  prettyTypeAnn x t = x <+> (cig $ ":" <+> (cpretty t))

instance (Show a, CPretty a) => TypeAnn (TypeSchemeT a) where
  prettyTypeAnn x (MonoType t) = x <+> (cig $ ":" <+> (cpretty t))
  prettyTypeAnn x (PolyType ts t) =
    x <+> (cig $ ":" <+> ((ckw "forall") <+> (hsep $ map (cpretty . TVar) ts) <+> "." <+> cpretty t))

instance CPretty Builtin where
  cpretty BAdd = cbi "$$add"
  cpretty BEq = cbi "$$eq"

nst :: Doc a -> Doc a
nst = nest 2

hng :: Doc a -> Doc a
hng = hang 2

prettyDeps :: Set Ident -> [CDoc]
prettyDeps deps =
  if S.null deps
  then []
  else [cig $ enclose "{" "}" $ go $ S.toList deps]
  where
    go :: [Ident] -> CDoc
    go [] = emptyDoc
    go [x] = cpretty x
    go (x0:x1:xs) = (cpretty x0) <> "," <> (go $ x1:xs)

instance (Show t, TypeAnn t) => CPretty (Binding t) where
  cpretty (Binding _ n _ deps b) =
    case b of
      Val e -> "." <+> (align $ sep $ [cdf $ cpretty n]
                                        ++ prettyDeps deps
                                        ++ [nst $ sep ["=", cpretty e]])
      Fun f -> "." <+> cpretty f

instance (Show t, TypeAnn t) => CPretty (Function t) where
  cpretty (Function n t args _ deps b) =
    align $ sep $ [(hsep $ (cdf $ cpretty n):argsDoc) `prettyTypeAnn` t]
                    ++ prettyDeps deps
                    ++ [nst $ sep ["=", cpretty b]]
    where
      argsDoc :: [CDoc]
      argsDoc =
        if null args
        then ["()"]
        else map (clc . cpretty . fst) args

instance (Show t, TypeAnn t) => CPretty (Pat t) where
  cpretty (PHole t) = (cig $ "_") `prettyTypeAnn` t
  cpretty (PLit t l) = (cpretty l) `prettyTypeAnn` t
  cpretty (PBinding t x) = (clc $ cpretty x) `prettyTypeAnn` t
  cpretty (PCons t x ps) = (parens $ hsep $ (ccn $ cpretty x) : (map cpretty ps)) `prettyTypeAnn` t

instance (Show t, TypeAnn t) => CPretty (Case t) where
  cpretty (Case p bs arm) = "|" <+> (hng $ sep $ [cpretty p]
                                                  ++ bsDoc
                                                  ++ [hng $ sep $ ["->", (cpretty arm)]])
    where
        bsDoc =
            if null bs
            then []
            else [cig $ enclose "{" "}" $ go bs]
        binding (x, t) = (cpretty x) <+> ":" <+> (cpretty t)
        go [] = emptyDoc
        go [x] = binding x
        go (x0:x1:xs) = (binding x0) <> "," <> (go $ x1:xs)

instance (Show t, TypeAnn t) => CPretty (Expr t) where
  cpretty (ELit t l) = (cpretty l) `prettyTypeAnn` t
  cpretty (ETup t es) = (tupled $ map cpretty es) `prettyTypeAnn` t
  cpretty (EBuiltin _ b) = cpretty b
  cpretty (EIdent t x) = (clc $ cpretty x) `prettyTypeAnn` t
  cpretty (EApp t e es) = (parens $ hng $ sep $ map (group . cpretty) (e:es)) `prettyTypeAnn` t
  cpretty (ELet _ bs e) = parens $ align $ sep $ (cpretty e) : (map cpretty bs)
  cpretty (EIf t e0 e1 e2) = align $ vsep [ (ckw "if") <+> (cpretty e0)
                                          , (ckw "then") <+> (hng $ cpretty e1)
                                          , (ckw "else") <+> (hng $ cpretty e2) ] `prettyTypeAnn` t
  cpretty (ECase t e0 cs) = (align $ sep $ (cpretty e0):(map cpretty cs)) `prettyTypeAnn` t
  cpretty (ELocal t x) = (clc $ cpretty x) `prettyTypeAnn` t
  cpretty (EGlobal t x) = (cgl $ cpretty x) `prettyTypeAnn` t
  cpretty (ECons t x) = parens $ (ccn $ cpretty x) `prettyTypeAnn` t

instance CPretty PathItem where
  cpretty (PathItem ps h alias) = hsep $ path : al
    where
      al =
        case alias of
          Nothing -> []
          Just x -> ["=" <+> (cpretty x)]
      path :: CDoc
      path = go ps h ""
      go (p0:p1:ps') hd r = go (p1:ps') hd (r <> (cpretty p0) <> "/")
      go (p:ps') hd r = go ps' hd (r <> (cpretty p))
      go [] Nothing r = r
      go [] (Just Nothing) r = r <> "/*"
      go [] (Just (Just ns)) r = r <> "/" <> (tupled $ map cpretty ns)

instance CPretty TypeCons where
  cpretty (TypeCons n ms) = "|" <+> (hng $ sep $ (ccn $ cpretty n):(map (cty . cpretty) ms))

instance CPretty TypeBody where
  cpretty (TBConses cs) = align $ vsep $ map cpretty cs
  cpretty (TBCType c) = (cbi "$$ctype") <+> (cty $ cpretty c)
  cpretty (TBAlias n) = cty $ cpretty n

instance CPretty TypeDef where
  cpretty (TypeDef n prs recGroup b) =
    ":" <+> (sep $ (cty $ cpretty n):(map (clc . cpretty) prs)
                     ++ (prettyDeps recGroup)
                     ++ [align $ sep ["=", cpretty b]])

instance (Show t, TypeAnn t) => CPretty (Module t) where
  cpretty (Module n im ex ts is) =
    vsep $ (cdf $ cpretty n) : (exDoc ++ imDoc ++ (map cpretty ts) ++ (map cpretty is))
    where
      imDoc = map (\x -> "<-" <+> (cpretty x)) im
      exDoc = map (\x -> "->" <+> (cpretty x)) ex


block :: [Doc a] -> Doc a
block ds = (nst $ vsep $ "{":ds) <> line <> "}" <> line

braced :: [Doc a] -> Doc a
braced = encloseSep lbrace rbrace comma

instance CPretty IRRecord where
  cpretty (IRRecord n fs) =
    (ccn $ cpretty n) <+> (braced $ map (\(t, x ) -> (cpretty x) <+> ":" <+> (cpretty t)) fs)

instance CPretty IRTypeBody where
  cpretty (IREnumType es) = (ckw "enum") <+> (braced $ map (ccn . cpretty) es)
  cpretty (IRStructType r) = (ckw "struct") <+> (cpretty r)
  cpretty (IRTaggedType rs) = align $ vsep $ map (\r -> (ckw "tag") <+> (cpretty r)) rs
  cpretty (IRCType c) = (ckw "ctype") <+> (cbi $ cpretty c)
  cpretty (IRFunType t ts) = (ckw "fptr") <+> (tupled $ map cpretty ts) <+> "->" <+> (cpretty t)
  cpretty (IRTypeAlias t) = (ckw "alias") <+> (cpretty t)

instance CPretty IRTypeDef where
  cpretty (IRTypeDef n rg isBoxed b) =
    hsep $ [ if isBoxed then (ckw "ref-type") else (ckw "val-type")
           , cty $ cpretty n, cig $ braced $ map cpretty $ S.toList rg, hng $ hsep ["=", cpretty b] ]

instance CPretty Operator where
  cpretty OpAdd = cbi "+"
  cpretty OpEq = cbi "=="
  cpretty OpAnd = cbi "&&"

instance CPretty IRLit where
  cpretty (IRInt i) = clt $ cpretty i
  cpretty IRVoid = clt "()"

instance CPretty IRExpr where
  cpretty (IRVar x) = clc $ cpretty x
  cpretty (IROp o es) = (cbi $ cpretty o) <> (tupled $ map cpretty es)
  cpretty (IRCall x es) = (cgl $ cpretty x) <> (tupled $ map cpretty es)
  cpretty (IRUnbox e) = (ckw "unbox") <> (parens $ cpretty e)
  cpretty (IRCons t x es) = (ccn $ (cpretty t) <> "/" <> (cpretty x)) <> (tupled $ map cpretty es)
  cpretty (IRLit l) = cpretty l
  cpretty (IRField e x) = (cpretty e) <> "." <> (cpretty x)
  cpretty (IRCheckVariant e x) = (ccn $ (cpretty x) <> "?") <+> (cpretty e)

instance CPretty IRStmt where
  cpretty (IRDef t n mX) = hsep $ [ckw "var", clc $ cpretty n, ":", cpretty t] ++ xDoc
    where
      xDoc =
        case mX of
          Nothing -> []
          Just x -> ["=" <+> (cpretty x)]
  cpretty (IRSet x e) = hsep $ [clc $ cpretty x, "<-", cpretty e]
  cpretty (IREval e) = cpretty e
  cpretty (IRBox t n e) =
    hsep $ [ckw "var", clc $ cpretty n, ":", cpretty t,  "=", ckw "box", cpretty e]
  cpretty (IRReturn e) = hsep $ [ckw "return", cpretty e]
  cpretty (IRIf e0 st0 [th@(IRIf _ _ _)]) =
    hsep $ [ ckw "if", cpretty e0
           , block $ map cpretty st0
           , ckw "else", cpretty th ]
  cpretty (IRIf e st0 st1) = hsep $ [ ckw "if", cpretty e
                                   , block $ map cpretty st0
                                   , ckw "else", block $ map cpretty st1 ]
  cpretty (IRPanic x) = hsep $ [ckw "panic", enclose "\"" "\"" $ cpretty x]


instance CPretty IRFunc where
  cpretty (IRFunc n _ ret args b) =
    (ckw "func") <+> (cdf $ cpretty n) <> argsDoc <+> "->" <+> (cpretty ret) <+> (block $ map cpretty b)
     where
       argsDoc = tupled $ map (\(x, t) -> (clc $ cpretty x) <+> ":" <+> (cpretty t)) args

instance CPretty IRType where
  cpretty (IRType t) = cty $ cpretty t
  cpretty IRBoxType = cbi "$$BOX-TYPE"

instance CPretty IRVarDecl where
  cpretty (IRVarDecl n _ t) = (ckw "var") <+> (cpretty n) <+> ":" <+> (cpretty t)

instance CPretty IRProgram where
  cpretty (IRProgram n tys fns vs init) =
    (ckw "module") <+> (cdf $ cpretty n) <> line
      <> line <> (vsep $ map cpretty tys) <> line
      <> line <> (vsep $ map cpretty vs) <> line
      <> line <> ((ckw "init") <+> (block $ map cpretty init)) <> line
      <> line <> (vsep $ map cpretty fns)
