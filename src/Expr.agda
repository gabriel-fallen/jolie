module Expr where

open import Data.Maybe using (Maybe; just; nothing)
open import Variable


-- TODO: add logic operations and, or
data BinOp : Set where
  plus minus mult div power : BinOp

data Expr : Set where
  var : Variable → Expr
  binary : BinOp → Expr → Expr → Expr
  constant : Variable.Value → Expr
