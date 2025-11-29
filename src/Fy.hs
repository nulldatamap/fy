{-# LANGUAGE OverloadedStrings, FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveAnyClass, DeriveGeneric, StandaloneDeriving, FunctionalDependencies, MultiParamTypeClasses #-}
module Fy
    ( compileAndRun
    ) where

import Debug.Trace (trace, traceStack)
import GHC.Stack (HasCallStack, prettyCallStack, callStack)

import Prelude hiding (lookup, lines)
import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T
import System.Exit
import System.Environment
import qualified Data.Text.IO as TIO
import System.Process hiding (env)
import qualified Data.Set as S
import Data.Hashable (Hashable)
import Data.Set (Set)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.List (intersperse, intercalate, partition)
import Data.Maybe (fromMaybe, maybeToList)
import Data.Char
import Control.Monad (when, foldM, unless)
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.RWS
import Data.Graph (stronglyConnComp, SCC(..))
import qualified Data.HashMap.Strict as M

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Fy.Types
import Fy.Ast
import Fy.Parser
import Fy.Naming
import Fy.Typing
import Fy.Ir
import Fy.Lowering
import Fy.Emit

-- NEXT:
-- - Fix parsing
-- TODO:
-- - Duplicate name check
-- - Guards?
-- - Zero types
-- - Tuples
-- - Function pointer types
-- - Parametric types
-- - Boxed types
-- - Toplevel functions?
-- - Lambdas
-- - Closures
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
        Right fn -> do
            let types = pTypeDefs p
            case infer types fn of
                Left err -> putStrLn $ show err
                Right ast -> do
                  let ir = lowerToIR types ast
                  let outF = f ++ ".c"
                  let out = emitProgram ir
                  TIO.writeFile outF out
                  callProcess "tcc/tcc.exe" ["-I", "./tcc/include", "-run", outF]
