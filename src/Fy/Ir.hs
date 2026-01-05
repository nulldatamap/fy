module Fy.Ir
  ( Operator(..)
  , IRFPtrType(..)
  , IRType(..), IRTypeDef(..), IRRecord(..), IRTypeBody(..)
  , IRVarDecl(..), IRLit(..), IRExpr(..), IRStmt(..), IRFunc(..)
  , IRProgram(..), Publicity(..)
  , irtUnit, irtInt
  ) where


import Data.Text (Text)
import Data.Set (Set)

import Fy.Types
import Fy.Ast (Publicity(..))

data Operator = OpAdd
              | OpEq
              | OpAnd
              deriving (Show, Eq)

data IRFPtrType = IRFPtrType IRType [IRType]
  deriving (Show, Eq)

data IRType = IRType Ident
            | IRCloType IRFPtrType
            | IRBoxType
  deriving (Show, Eq)

data IRRecord = IRRecord Ident [(IRType, Ident)]
  deriving (Show)

data IRTypeBody = IREnumType [Ident]
                | IRStructType IRRecord
                | IRTaggedType [IRRecord]
                | IRCType Text
                | IRFunType IRFPtrType
                | IRTypeAlias IRType
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
            | IRInvoke IRFPtrType IRExpr [IRExpr]
            | IRClosure Ident (Maybe IRExpr)
            | IRCons IRType Ident [IRExpr]
            | IRLit IRLit
            | IREnv Ident
            | IRUnbox (Maybe IRType) IRExpr
            | IRField IRExpr Ident
            | IRCheckVariant IRExpr Ident
            deriving (Show)

data IRStmt = IRDef IRType Ident (Maybe IRExpr)
            | IRBox IRType Ident IRType IRExpr
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
                     , irfDeps  :: Set Ident
                     , irfEnv   :: Maybe IRType
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

irtInt :: IRType
irtInt = IRType (Ident "int" [] Nothing)

irtUnit :: IRType
irtUnit = IRType (Ident "()" [] Nothing)
