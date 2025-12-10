module Fy
    ( compileAndRun
    ) where


import Prelude hiding (lookup, lines)
import qualified Data.Text.IO as TIO
import System.Exit
import System.Process
import Text.Megaparsec
import Prettyprinter
import Prettyprinter.Util

import Fy.Types
import Fy.Ast
import Fy.Parser
import Fy.Naming
import Fy.Typing
import Fy.Mono
import Fy.Lowering
import Fy.Emit

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

compileAndRun :: String -> IO ()
compileAndRun f = do
  src <- TIO.readFile f
  case parseModule f src of
    Left err -> do
      putStrLn $ errorBundlePretty err
      exitFailure
    Right m -> do
      putDocW 80 $ (pretty m) <+> line
      case namingCheck m of
        Left err -> putStrLn $ show err
        Right nm -> do
            putDocW 80 $ (pretty nm) <+> line
            case infer nm of
                Left err -> putStrLn $ show err
                Right tm -> do
                  putDocW 80 $ (pretty tm) <+> line
                  let mm = monomorphise tm
                  putDocW 80 $ (pretty mm) <+> line
                  let ir = lowerToIR mm
                  let outF = f ++ ".c"
                  let out = emitProgram ir
                  TIO.writeFile outF out
                  callProcess "tcc/tcc.exe" ["-I", "./tcc/include", "-run", outF]
