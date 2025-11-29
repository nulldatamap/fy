module Fy.Emit
  ( emitProgram
  ) where

import Fy.Types
import Fy.Ir
import Fy.Typing

import Prelude hiding (lookup, lines)
import Data.Text (Text)
import qualified Data.Text as T
import Data.List (intersperse, intercalate, partition)
import Data.Maybe (fromMaybe, maybeToList)
import Control.Monad (when, foldM, unless)
import Control.Monad.RWS

type Identation = Int

type Emitter a = RWS Identation [Text] () a


runEmitter :: Emitter () -> Text
runEmitter m = T.concat $ snd $ evalRWS m 0 ()

indented :: Emitter a -> Emitter a
indented m = local (+1) m

indent :: Emitter ()
indent = do
  d <- ask
  emit $ T.replicate d "  "

line :: Text -> Emitter ()
line l = tell [ l, "\n" ]

lines :: [Text] -> Emitter ()
lines ls = do
  tell $ intersperse "\n" ls
  tell ["\n"]

around :: Text -> Text -> Emitter a -> Emitter a
around o c m = do
  emit o
  r <- m
  emit c
  return r

parens :: Emitter a -> Emitter a
parens = around "(" ")"

seperated :: Text -> (a -> Emitter ()) -> [a] -> Emitter ()
seperated _ _ []  = return ()
seperated _ f [x] = f x
seperated sep f (x0:x1:xs) = (f x0) >> (emit sep) >> (seperated sep f (x1:xs))

emit :: Text -> Emitter ()
emit x = tell [ x ]

braceBlock :: Emitter a -> Emitter a
braceBlock m = do
  line "{"
  r <- indented m
  indent
  emit "}"
  return r

emitProgram :: IRProgram -> Text
emitProgram p = runEmitter $ do
  lines [ "#include <stdio.h>"
        , "#include <stdbool.h>"
        , "#include <stdlib.h>"
        , ""
        ]
  mapM_ (\td -> (emitTypeDef td) >> (emitConses td)) $ irpTypes p
  mapM_ emitFunction $ irpFuncs p
  lines [ "int main(int argc, const char** argv) {"
        , "  printf(\"Result: %d\\n\", __fy_main());"
        , "  return 0;"
        , "}" ]

emitFunction  :: IRFunc -> Emitter ()
emitFunction f = do
    indent
    emitType $ irfRetTy f
    emit " "
    emitIdent $ irfName f
    parens $ do
      let prms = filter ((/= tUnit) . snd) $ irfArgs f
      seperated ", " (\(n, t) -> (emitType t) >> (emit " ") >> (emitIdent n)) prms
    emit " "
    braceBlock $ do
      emitStmts $ irfBody f
    emit "\n\n"

emitStmts :: [IRStmt] -> Emitter ()
emitStmts [] = return ()
emitStmts (s:ss) = indent >> (emitStmt s) >> (emit "\n") >> (emitStmts ss)

emitStmt :: IRStmt -> Emitter ()
emitStmt (IRDef t x mE) = do
  emitType t
  emit " "
  emitIdent x
  mapM_ (\e -> (emit " = ") >> emitExpr e) mE
  emit ";"
emitStmt (IRSet x e) = (emitIdent x) >> (emit " = ") >> (emitExpr e) >> (emit ";")
emitStmt (IREval e) = (emitExpr e) >> (emit ";")
emitStmt (IRReturn e) = (emit "return ") >> (emitExpr e) >> (emit ";")
emitStmt (IRIf e0 sts1 sts2) = do
  emit "if("
  emitExpr e0
  emit ") "
  braceBlock $ emitStmts sts1
  emit " else "
  case sts2 of
    [s@(IRIf _ _ _)] -> emitStmt s
    _ -> braceBlock $ emitStmts sts2
emitStmt (IRPanic msg) = do
  emit "/* PANIC! */ printf(\""
  emit msg
  emit "\"); exit(1); "

emitExpr :: IRExpr -> Emitter ()
emitExpr (IRVar x) = emitIdent x
emitExpr (IRLit l) =
  case l of
    IRInt x -> emit $ T.pack $ show x
    IRVoid -> emit "/*void*/"
emitExpr (IROp OpAnd []) = emit "1"
emitExpr (IROp OpAnd [x]) = emitExpr x
emitExpr (IROp OpAnd xs) = seperated " && " emitExpr xs
emitExpr (IROp o [x, y]) =
    case o of
        OpAdd -> parens ((emitExpr x) >> (emit " + ") >> (emitExpr y))
        OpEq  -> parens ((emitExpr x) >> (emit " == ") >> (emitExpr y))
emitExpr e@(IROp _ _) = error $ "Invalid operator: " ++ (show e)
emitExpr (IRCons t x es) = do
  emit "MK_"
  emitIdent t
  emit "_"
  emitIdent x
  parens $ seperated ", " emitExpr es
emitExpr (IRCall x es) = do
  emitIdent x
  parens $ seperated ", " emitExpr es
emitExpr (IRField e f) = do
  let mParen = case e of
                 IRField _ _ -> id
                 IRVar _     -> id
                 _           -> parens
  mParen $ emitExpr e
  emit "."
  emitIdent f
emitExpr (IRCheckVariant e t v) = do
  parens $ do
    emitExpr (IRField e variantField)
    emit " == "
    emitIdent $ variant t v

emitIdent :: Ident -> Emitter ()
emitIdent x = emit $ canonicalId x

emitType :: IRType -> Emitter ()
emitType t@(TVar _) = error $ "Type variable present at emti-stage: " ++ (show t)
emitType (TCons (Ident "int" Nothing Nothing) []) = emit "int"
emitType (TCons (Ident "bool" Nothing Nothing) []) = emit "bool"
emitType (TCons (Ident "()" Nothing Nothing) []) = emit "void"
emitType (TCons x []) = emitIdent x
emitType t = error $ "Unsupported type: " ++ (show t)

emitEnum :: Ident -> Bool -> [Ident] -> Emitter ()
emitEnum t isVariant vs = do
    indent
    emit "typedef enum "
    braceBlock $ do
      mapM_ (\n -> indent >> (emitIdent $ variant t n) >> line ",") vs
    emit " "
    emitIdent t
    when isVariant $ emit "__variant"
    line ";\n"
emitStruct :: Ident -> IRRecord -> Emitter ()
emitStruct n (IRRecord c fs) = do
  indent
  emit "struct "
  braceBlock $ do
      mapM_ (\(t, f) -> do
              indent
              emitType t
              emit " "
              emitIdent f
              line ";")
        fs
  emit " "
  emitIdent n
  line ";"

emitTypeDef :: IRTypeDef -> Emitter ()
emitTypeDef (IRCType t ct) = do
  emit "typedef "
  emit ct
  emit " "
  emitIdent t
  line ";\n"
emitTypeDef (IRStructType t r) = do
  emit "typedef "
  emitStruct t r
  line ""
emitTypeDef (IREnumType t variants) = emitEnum t False variants
emitTypeDef (IRTaggedType t rs) = do
  emitEnum t True $ map (\(IRRecord v _) -> v) rs
  indent
  emit "typedef struct "
  braceBlock $ do
    indent
    emitIdent t
    emit "__variant "
    emitIdent variantField
    line ";"
    indent
    emit "union "
    braceBlock $
      mapM_ (\r@(IRRecord c _) -> emitStruct c r) rs
    line ";"
  emit " "
  emitIdent t
  line ";\n"

emitConses :: IRTypeDef -> Emitter ()
emitConses (IRCType _ _) = return ()
emitConses (IREnumType t variants) = do
  mapM_ (\v -> do
            emit "#define MK_"
            emitIdent t
            emit "_"
            emitIdent v
            emit "() "
            emitIdent $ variant t v
            line "") variants
  line ""
emitConses (IRStructType t (IRRecord c fs)) = do
  emit "#define MK_"
  emitIdent t
  emit "_"
  emitIdent c
  let args = take (length fs) $ enumeratedIds "__arg"
  parens $ seperated ", " emitIdent args
  emit " "
  parens $ emitIdent t
  emit " {"
  seperated ", " emitIdent args
  line " }\n"
emitConses (IRTaggedType t rs) = mapM_ emitCons rs >> line ""
  where
    emitCons (IRRecord c fs) = do
      emit "#define MK_"
      emitIdent t
      emit "_"
      emitIdent c
      let args = take (length fs) $ enumeratedIds "__arg"
      parens $ seperated ", " emitIdent args
      emit " "
      parens $ emitIdent t
      emit " {."
      emitIdent variantField
      emit " = "
      emitIdent $ variant t c
      emit ", ."
      emitIdent c
      emit " = {"
      seperated ", " emitIdent args
      emit "}"
      line "}"
