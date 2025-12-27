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
import Prettyprinter.Render.Terminal

import Fy.Ast
import Fy.Parser
import Fy.Naming
import Fy.Typing
import Fy.Normalize
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

instance CPretty Repr where
  cpretty (RSource _ src) = cpretty src
  cpretty (RUAst m) = cpretty m
  cpretty (RTAst m) = cpretty m
  cpretty (RIr m)   = cpretty m
  cpretty (RC m)    = cpretty m

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
-- - Bug fixes:
--   - Fix nilary vs called-with-unit
-- - Language features:
--   - Type annotations
--   - Type parameter usage (for types)
--   - Name aliases
--   - Module system
--   - Guards?
--   - Zero types
--   - Tuples
--   - Records
--   - @-patterns
--   - "Effects"
--   - Effect handlers
--   - Traits
--   - Trait boxing
--   - Infix operators
--   - Pipe operators
--   - GC Roots
--   - GC
--   - Pattern completeness checks
--   - Binding pattern-matching
-- - Optimizations:
--   - Better boxing heuristics
--   - Dead code elim
--   - Escape analysis
--   - Tail calls
--   - Shrinking
--   - Defunctionalization?
--   - Lambda lifting
-- - QoL:
--   - Source locations
--   - Error context


passes :: [Pass]
passes =
  [ sourcePass "Parsing"          parseModule            RUAst errorBundlePretty
  , uastPass   "Name resolution"  namingCheck            RUAst show
  , uastPass   "Type inference"   infer                  RTAst show
  , tastPass   "Normalization"    (Right . normalize)    RTAst id
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
            putDoc $ (cpretty rOut) <> line
          return rOut
    shouldPrint = coPrintPasses opts

compileAndRun :: String -> IO ()
compileAndRun f = do
  let opts = CompilerOpts True
  src <- TIO.readFile f
  outR <- runPasses opts (RSource f src) passes
  case outR of
    RC out -> do
      let outF = f ++ ".c"
      TIO.writeFile outF out
      when (coPrintPasses opts) $
        putStrLn "\n========= Execution"
      callProcess "tcc/tcc.exe" ["-I", "./tcc/include", "-run", outF]
    _ -> error "Final pass result wasn't C source code"
