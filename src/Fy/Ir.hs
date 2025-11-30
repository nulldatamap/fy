module Fy.Ir
  ( Operator(..)
  , IRType(..), IRTypeDef(..), IRRecord(..)
  , IRLit(..), IRExpr(..), IRStmt(..), IRFunc(..)
  , IRProgram(..)
  , typeDefName, irtUnit
  ) where


import Data.Text (Text)

import Fy.Types

data Operator = OpAdd
              | OpEq
              | OpAnd
              deriving (Show, Eq)

data IRType = IRType Ident
  deriving (Show, Eq)

data IRRecord = IRRecord Ident [(IRType, Ident)]
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
            | IRCons IRType Ident [IRExpr]
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

irtUnit :: IRType
irtUnit = IRType (Ident "()" [] Nothing)

typeDefName :: IRTypeDef -> Ident
typeDefName (IREnumType n _) = n
typeDefName (IRStructType n _) = n
typeDefName (IRTaggedType n _) = n
typeDefName (IRCType n _) = n
