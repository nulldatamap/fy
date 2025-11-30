module Fy
    ( compileAndRun
    ) where


import Prelude hiding (lookup, lines)
import qualified Data.Text.IO as TIO
import System.Exit
import System.Process
import Text.Megaparsec

import Fy.Parser
import Fy.Naming
import Fy.Typing
import Fy.Lowering
import Fy.Emit

-- NEXT:
-- - Fix parsing
-- TODO:
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
  case parseProgram f src of
    Left err -> do
      putStrLn $ errorBundlePretty err
      exitFailure
    Right ast' -> do
      let p = ast'
      case namingCheck p of
        Left err -> putStrLn $ show err
        Right (types, fn) -> do
            case infer types fn of
                Left err -> putStrLn $ show err
                Right ast -> do
                  let ir = lowerToIR types ast
                  let outF = f ++ ".c"
                  let out = emitProgram ir
                  TIO.writeFile outF out
                  callProcess "tcc/tcc.exe" ["-I", "./tcc/include", "-run", outF]
