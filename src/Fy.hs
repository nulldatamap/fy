module Fy
    ( compileAndRun
    ) where


import Prelude hiding (lookup, lines)
import qualified Data.Text.IO as TIO
import System.Exit
import System.Process
import Text.Megaparsec
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (when, foldM)
import Prettyprinter
import Prettyprinter.Util

import Fy.Types
import Fy.Ast
import Fy.Parser
import Fy.Naming
import Fy.Typing
import Fy.Mono
import Fy.Ir
import Fy.Lowering
import Fy.Emit
import Fy.Pretty

data Repr = RSource String Text
          | RUAst UModule
          | RTAst TModule
          | RIr IRProgram
          | RC Text

instance Pretty Repr where
  pretty (RSource f src) = "-- " <> (pretty f) <> line <> (pretty src)
  pretty (RUAst m) = pretty m
  pretty (RTAst m) = pretty m
  pretty (RIr m)   = viaShow m
  pretty (RC m)    = pretty m

data Pass = Pass { pName :: Text
                 , pRun  :: Repr -> Either String Repr }

data CompilerOpts = CompilerOpts { coPrintPasses :: Bool }

liftResult :: Either err out -> (out -> Repr) -> (err -> String) -> Either String Repr
liftResult (Left err) _ f = Left $ f err
liftResult (Right out) f _ = Right $ f out

sourcePass :: Text -> (String -> Text -> Either err out) -> (out -> Repr) -> (err -> String) -> Pass
sourcePass n p out err =
  Pass n (\repr ->
            case repr of
              RSource f src -> liftResult (p f src) out err
              _ -> error $ "Expect source input for pass: " ++ (show n))

uastPass :: Text -> (UModule -> Either err out) -> (out -> Repr) -> (err -> String) -> Pass
uastPass n p out err =
  Pass n (\repr ->
            case repr of
              RUAst m -> liftResult (p m) out err
              _ -> error $ "Expect u-ast input for pass: " ++ (show n))

tastPass :: Text -> (TModule -> Either err out) -> (out -> Repr) -> (err -> String) -> Pass
tastPass n p out err =
  Pass n (\repr ->
            case repr of
              RTAst m -> liftResult (p m) out err
              _ -> error $ "Expect t-ast input for pass: " ++ (show n))

irPass :: Text -> (IRProgram -> Either err out) -> (out -> Repr) -> (err -> String) -> Pass
irPass n p out err =
  Pass n (\repr ->
            case repr of
              RIr m -> liftResult (p m) out err
              _ -> error $ "Expect ir input for pass: " ++ (show n))

-- TODO:
-- - Deal with non-function bindings
-- - Type parameter usage (for types)
-- - Source locations
-- - Error context
-- - Name aliases
-- - Module system
-- - Guards?
-- - Zero types
-- - Tuples
-- - @-patterns
-- - Function pointer types
-- - Boxed types
-- - Toplevel functions?
-- - Lambdas
-- - Closures
-- - "Effects"
-- - Effect handlers
-- - Traits
-- - Trait boxing
-- - Pipe operators

passes :: [Pass]
passes =
  [ sourcePass "Parsing"          parseModule            RUAst errorBundlePretty
  , uastPass   "Name resolution"  namingCheck            RUAst show
  , uastPass   "Type inference"   infer                  RTAst show
  , tastPass   "Monomorphisation" (Right . monomorphise) RTAst id
  , tastPass   "Lowering"         (Right . lowerToIR)    RIr   id
  , irPass     "Emit C"           (Right . emitProgram)  RC    id ]

runPasses :: CompilerOpts -> Repr -> [Pass] -> IO Repr
runPasses opts r ps = foldM runPass r ps
  where
    runPass rIn p = do
      when shouldPrint $
        putStrLn $ "\n========= " ++ (T.unpack $ pName p)
      case (pRun p) rIn of
        Left err -> do
          when shouldPrint $ putStrLn $ "Pass \"" ++ (T.unpack $ pName p) ++ "\" failed"
          putStrLn err
          exitFailure
        Right rOut -> do
          when shouldPrint $
            putDocW 100 $ (pretty rOut) <> line
          return rOut
    shouldPrint = coPrintPasses opts

compileAndRun :: String -> IO ()
compileAndRun f = do
  src <- TIO.readFile f
  outR <- runPasses (CompilerOpts True) (RSource f src) passes
  case outR of
    RC out -> do
      let outF = f ++ ".c"
      TIO.writeFile outF out
      callProcess "tcc/tcc.exe" ["-I", "./tcc/include", "-run", outF]
    _ -> error "Final pass result wasn't C source code"
