module Expr where

open import Variable


data BinOp : Set where
  plus : BinOp
  minus : BinOp
  mult : BinOp
  div : BinOp
  power : BinOp

data Expr : Set where
  var : Variable → Expr
  binary : BinOp → Variable → Variable → Expr
  constant : Variable.Value → Expr
