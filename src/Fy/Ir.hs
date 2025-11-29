module Fy.Ir
  ( Operator(..)
  , IRType(..), IRTypeDef(..), IRRecord(..)
  , IRLit(..), IRExpr(..), IRStmt(..), IRFunc(..)
  , IRProgram(..)
  ) where

import Data.Text (Text)

import Fy.Types

data Operator = OpAdd
              | OpEq
              | OpAnd
              deriving (Show, Eq)

type IRType = Type

data IRRecord = IRRecord Ident [(Type, Ident)]
  deriving (Show)

data IRTypeDef = IREnumType Ident [Ident]
               | IRStructType Ident IRRecord
               | IRTaggedType Ident [IRRecord]
               | IRCType Ident Text
               deriving Show

data IRLit = IRInt Integer
           | IRVoid
           deriving (Show)

data IRExpr = IRVar Ident
            | IROp Operator [IRExpr]
            | IRCall Ident [IRExpr]
            | IRCons Ident Ident [IRExpr]
            | IRLit IRLit
            | IRField IRExpr Ident
            | IRCheckVariant IRExpr Ident Ident
            deriving (Show)

data IRStmt = IRDef IRType Ident (Maybe IRExpr)
            | IRSet Ident IRExpr
            | IREval IRExpr
            | IRReturn IRExpr
            | IRIf IRExpr [IRStmt] [IRStmt]
            | IRPanic Text
            deriving (Show)

data IRFunc = IRFunc { irfName  :: Ident
                     , irfRetTy :: IRType
                     , irfArgs  :: [(Ident, IRType)]
                     , irfBody  :: [IRStmt] }
            deriving (Show)

data IRProgram = IRProgram { irpTypes :: [IRTypeDef], irpFuncs :: [IRFunc] }
            deriving (Show)
