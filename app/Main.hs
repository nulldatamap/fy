module Main (main) where


import Fy

import System.Environment

main :: IO ()
main = do
  args <- getArgs
  case args of
    [f] -> compileAndRun f
    _   -> error "Expected a single input file-name"
