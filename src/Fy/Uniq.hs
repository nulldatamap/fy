module Fy.Uniq
  (runUniq, uniqExpr, uniqBinding)
  where

import Fy.Types hiding (subst)
import Fy.Ast

import qualified Data.HashMap.Strict as M
import Control.Monad.State.Strict

data UniqSt = UniqSt { ustNext   :: Int
                     , ustSubsts :: M.HashMap Ident Ident }

type Uniq = State UniqSt

type Pass = AstVisitor Uniq Type

runUniq :: Int -> Uniq a -> (a, Int)
runUniq i m =
  let (r, st) = runState m $ UniqSt { ustNext = i
                                    , ustSubsts = M.empty }
  in (r, ustNext st)

uniq :: Ident -> Uniq Ident
uniq (Ident n ns _) = do
  i <- ustNext <$> get
  modify (\s -> s { ustNext = i + 1 })
  return $ Ident n ns $ Just i

intro :: [(Ident, Ident)] -> Uniq ()
intro xs =
  modify (\s -> s { ustSubsts = M.union (M.fromList xs) $ ustSubsts s })

subst :: Ident -> Uniq Ident
subst x = ((M.findWithDefault x x) . ustSubsts) <$> get

doExpr :: TExpr -> Uniq TExpr
doExpr e =
  case e of
    ELocal t x -> (ELocal t) <$> (subst x)
    ELet t bs e0 -> do
      bs' <- mapM (\b -> do
                     x' <- uniq $ bName b
                     return $ b { bName = x' })
               bs
      intro $ zipWith (\b b' -> (bName b, bName b')) bs bs'
      return $ ELet t bs' e0
    _ -> return e

pass :: Pass
pass = newVisitor { avPreExpr = doExpr }

uniqExpr :: TExpr -> Uniq TExpr
uniqExpr = visitExpr pass


uniqBinding :: TBinding -> Uniq TBinding
uniqBinding = visitBinding pass
