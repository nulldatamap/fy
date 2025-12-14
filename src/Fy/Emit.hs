module Fy.Emit
  ( emitProgram
  ) where


import Fy.Types
import Fy.Ir

import Prelude hiding (lookup, lines)
import Data.Text (Text)
import qualified Data.HashMap.Strict as M
import qualified Data.Text as T
import Data.List (intersperse)
import Control.Monad (when)
import Control.Monad.RWS

data EmitterSt = EmitterSt { estIndentation :: Int
                           , estTypes :: M.HashMap Ident IRTypeDef }

type Emitter a = RWS EmitterSt [Text] () a


runEmitter :: Emitter () -> Text
runEmitter m = T.concat $ snd $ evalRWS m (EmitterSt 0 M.empty) ()

indented :: Emitter a -> Emitter a
indented m = local (\st -> st { estIndentation = 1 + estIndentation st }) m

indent :: Emitter ()
indent = do
  d <- estIndentation <$> ask
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

withTypes :: [IRTypeDef] -> Emitter a -> Emitter a
withTypes tds m =
  local (\s -> s { estTypes = M.fromList $ map (\td -> (irtdName td, td)) tds }) m

emitProgram :: IRProgram -> Text
emitProgram p = runEmitter $ withTypes (irpTypes p) $ do
  lines [ "#include <stdio.h>"
        , "#include <stdbool.h>"
        , "#include <stdlib.h>"
        , ""
        , "typedef struct {} __fy_unit;"
        , "#define __FY_UNIT ((__fy_unit){})"
        , ""
        , "void* __fy_alloc(size_t sz) { return malloc(sz); }"
        , "#define ALLOC(__ARG_t, __ARG_x, __ARG_v) __ARG_t __ARG_x = (__ARG_t)__fy_alloc(sizeof(*__ARG_x)); *__ARG_x = __ARG_v;"
        ]
  emitTypeDefs $ irpTypes p
  mapM_ emitVarDecl $ irpVars p
  line ""
  mapM_ emitFunction $ irpFuncs p
  emitModuleInitializer (irpName p) $ irpInit p
  emit "\nint main(int argc, const char** argv)"
  braceBlock $ do
    indent
    emitIdent (irpName p)
    line "__init();"
    lines [ "  printf(\"Result: %d\\n\", __main());"
          , "  return 0;" ]
  line "\n"

emitItemExport :: Publicity -> Ident -> Emitter Ident
emitItemExport Private x = (emit "static ") >> (return x)
emitItemExport Public x = return x
emitItemExport (CExport cName) x = do
  emit "#define "
  emitIdent x
  emit " "
  line cName
  return $ mkId cName

emitVarDecl :: IRVarDecl -> Emitter ()
emitVarDecl (IRVarDecl x p t) = do
  x' <- emitItemExport p x
  emitType t
  emit " "
  emitIdent x'
  line ";"

emitModuleInitializer :: Ident -> [IRStmt] -> Emitter ()
emitModuleInitializer n sts = do
  emit "void "
  emitIdent n
  emit "__init() "
  braceBlock $ do
    emitStmts sts
  line ""

emitTypeDefs :: [IRTypeDef] -> Emitter ()
emitTypeDefs tds =
  mapM_ (\td -> do
            emitTypeDef td
            emitConses td)
    tds

emitFunction  :: IRFunc -> Emitter ()
emitFunction f = do
    indent
    fn' <- emitItemExport (irfPub f) (irfName f)
    emitType $ irfRetTy f
    emit " "
    emitIdent fn'
    parens $ do
      seperated ", " (\(n, t) -> (emitType t) >> (emit " ") >> (emitIdent n)) $ irfArgs f
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
emitStmt (IRBox t x e) = do
  emit "ALLOC"
  parens $ (emitType t) >> (emit ", ") >> (emitIdent x) >> (emit ", ") >> (emitExpr e)
  emit ";"

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

chainedOp :: Bool -> Text -> Text -> [IRExpr] -> Emitter ()
chainedOp _ _ base [] = emit base
chainedOp True _ _ [x] = emitExpr (x)
chainedOp False op _ [x] = error $ "Can't use chained op `" ++ (show op) ++ "` with only one argument: " ++ (show x)
chainedOp _ op _ xs = seperated op emitExpr xs

emitExpr :: IRExpr -> Emitter ()
emitExpr (IRVar x) = emitIdent x
emitExpr (IRLit l) =
  case l of
    IRInt x -> emit $ T.pack $ show x
    IRVoid -> emit "__FY_UNIT"
emitExpr (IROp OpAnd xs) = chainedOp True " && " "1" xs
emitExpr (IROp OpEq xs) = chainedOp False " == " "1" xs
emitExpr (IROp o [x, y]) =
    case o of
        OpAdd -> parens ((emitExpr x) >> (emit " + ") >> (emitExpr y))
emitExpr e@(IROp _ _) = error $ "Invalid operator: " ++ (show e)
emitExpr (IRCons (IRType tn) x es) = do
  emit "MK_"
  emitIdent' tn
  emit "_"
  emitIdent' x
  parens $ seperated ", " emitExpr es
emitExpr (IRCons t _ _) = error $ "Invalid cons type: " ++ (show t)
emitExpr (IRUnbox e) = parens $ emit "*" >> emitExpr e
emitExpr (IRCall x es) = do
  emitIdent x
  parens $ seperated ", " emitExpr es
emitExpr (IRField e f) = do
  let (mParen, s, e') = case e of
                          IRField _ _ -> (id, ".", e)
                          IRVar _     -> (id, ".", e)
                          IRUnbox e0  -> (id, "->", e0)
                          _           -> (parens, ".", e)
  mParen $ emitExpr e'
  emit s
  emitIdent' f
emitExpr (IRCheckVariant e v) = do
  parens $ do
    emitExpr (IRField e variantField)
    emit " == "
    emitIdent $ v

emitIdent' :: Ident -> Emitter ()
emitIdent' x = emit $ canonicalId x

emitIdent :: Ident -> Emitter ()
emitIdent x = emit "__" >> (emit $ canonicalId x)

emitType :: IRType -> Emitter ()
emitType (IRType (Ident "int" [] Nothing)) = emit "int"
emitType (IRType (Ident "bool" [] Nothing)) = emit "bool"
emitType (IRType (Ident "()" [] Nothing)) = emit "__fy_unit"
emitType (IRType x) = emitIdent x
emitType IRBoxType = emit "void*"

emitEnum :: Ident -> Bool -> [Ident] -> Emitter ()
emitEnum t isVariant vs = do
    indent
    emit "typedef enum "
    braceBlock $ do
      mapM_ (\n -> indent >> (emitIdent t) >> (emit "_") >> (emitIdent' $ n) >> line ",") vs
    emit " "
    emitIdent t
    when isVariant $ emit "__variant"
    line ";\n"
emitStruct' :: Bool -> Ident -> IRRecord -> Bool -> Emitter ()
emitStruct' isField n (IRRecord _ fs) isBoxed = do
  indent
  emit "struct "
  when isBoxed $ do
    emitIdent n
    emit "_unboxed "
  braceBlock $ do
      mapM_ (\(t, f) -> do
              indent
              emitType t
              emit " "
              emitIdent' f
              line ";")
        fs
  emit " "
  when isBoxed $ emit "*"
  if isField
  then emitIdent' n
  else emitIdent n
  line ";"

emitStruct :: Ident -> IRRecord -> Bool -> Emitter ()
emitStruct n r isBoxed = emitStruct' False n r isBoxed

emitTypeDef :: IRTypeDef -> Emitter ()
emitTypeDef (IRTypeDef t _ isBoxed b) = do
  case b of
    IRCType ct -> do
      emit "typedef "
      emit ct
      when isBoxed $ emit "*"
      emit " "
      emitIdent t
      line ";\n"
    IRStructType r -> do
      emit "typedef "
      emitStruct t r isBoxed
      line ""
    IREnumType variants -> emitEnum t False variants
    IRTaggedType rs -> do
      emitEnum t True $ map (\(IRRecord v _) -> v) rs
      indent
      emit "typedef struct "
      when isBoxed $ do
        emitIdent t
        emit "_unboxed "
      braceBlock $ do
        indent
        emitIdent t
        emit "__variant "
        emitIdent' variantField
        line ";"
        indent
        emit "union "
        braceBlock $
          mapM_ (\r@(IRRecord c _) -> emitStruct' True c r False) rs
        line ";"
      when isBoxed $ emit "*"
      emit " "
      emitIdent t
      line ";\n"
    IRFunType rt ts -> do
      emit "typedef "
      emitType rt
      emit " "
      parens $ emit "*" >> emitIdent t
      parens $ seperated ", " emitType ts
      line ";"
    IRTypeAlias at -> do
      emit "typedef "
      emitType at
      emit " "
      emitIdent t
      line ";"

emitConses :: IRTypeDef -> Emitter ()
emitConses (IRTypeDef tn _ isBoxed b) =
  case b of
    IRFunType _ _ -> return ()
    IRCType _ -> return ()
    IRTypeAlias _ -> return ()
    IREnumType variants -> do
        mapM_ (\v -> do
                    emit "#define MK_"
                    emitIdent' tn
                    emit "_"
                    emitIdent' v
                    emit "() "
                    emitIdent tn
                    emit "_"
                    emitIdent' $ v
                    line "") variants
        line ""
    IRStructType (IRRecord c fs) -> do
        emit "#define MK_"
        emitIdent' tn
        emit "_"
        emitIdent' c
        let args = take (length fs) $ enumeratedIds "__arg"
        parens $ seperated ", " emitIdent' args
        emit " "
        parens $ innerTn
        emit " {"
        seperated ", " emitIdent' args
        line " }\n"
    IRTaggedType rs -> mapM_ emitCons rs >> line ""
  where
    innerTn =
      if isBoxed
      then do
        emit "struct "
        emitIdent tn
        emit "_unboxed"
      else emitIdent tn
    emitCons (IRRecord c fs) = do
      emit "#define MK_"
      emitIdent' tn
      emit "_"
      emitIdent' c
      let args = take (length fs) $ enumeratedIds "__arg"
      parens $ seperated ", " emitIdent' args
      emit " "
      parens $ innerTn
      emit " {."
      emitIdent' variantField
      emit " = "
      emitIdent tn
      emit "_"
      emitIdent' c
      emit ", ."
      emitIdent' c
      emit " = {"
      seperated ", " emitIdent' args
      emit "}"
      line "}"
