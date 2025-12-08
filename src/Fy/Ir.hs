module Fy.Ir
  ( Operator(..)
  , IRType(..), IRTypeDef(..), IRRecord(..), IRTypeBody(..)
  , IRVarDecl(..), IRLit(..), IRExpr(..), IRStmt(..), IRFunc(..)
  , IRProgram(..), Publicity(..)
  , irtUnit
  ) where


import Data.Text (Text)
import Data.Set (Set)

import Fy.Types
import Fy.Ast (Publicity(..))

data Operator = OpAdd
              | OpEq
              | OpAnd
              deriving (Show, Eq)

data IRType = IRType Ident
  deriving (Show, Eq)

data IRRecord = IRRecord Ident [(IRType, Ident)]
  deriving (Show)

data IRTypeBody = IREnumType [Ident]
                | IRStructType IRRecord
                | IRTaggedType [IRRecord]
                | IRCType Text
                | IRFunType IRType [IRType]
                deriving Show

data IRTypeDef = IRTypeDef { irtdName :: Ident
                           , irtdRecursionGroup :: Set Ident
                           , irtdIsBoxed :: Bool
                           , irtdBody :: IRTypeBody }
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
                     , irfPub   :: Publicity
                     , irfRetTy :: IRType
                     , irfArgs  :: [(Ident, IRType)]
                     , irfBody  :: [IRStmt] }
            deriving (Show)

data IRVarDecl = IRVarDecl { irvdName :: Ident
                           , irvPub   :: Publicity
                           , irvdType :: IRType }
            deriving (Show)

data IRProgram = IRProgram { irpName  :: Ident
                           , irpTypes :: [IRTypeDef]
                           , irpFuncs :: [IRFunc]
                           , irpVars  :: [IRVarDecl]
                           , irpInit  :: [IRStmt] }
            deriving (Show)

irtUnit :: IRType
irtUnit = IRType (Ident "()" [] Nothing)
