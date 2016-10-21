module Typecheck where

open import Data.Maybe using (Maybe; just; nothing)
open import Function
open import Expr
open import Type
open import Behaviour
open import Variable


typecheck_behaviour : Γ → Behaviour → Maybe Γ
typecheck_behaviour env nil = just env
typecheck_behaviour env (if e b1 maybe_b2) =
  case e of λ
  {
    -- If conditional expression is variable
    (var v) →
      let ctx1 = typecheck_behaviour env b1 in
      {!!}
  ; _ → nothing
  }
typecheck_behaviour _ _ = nothing
