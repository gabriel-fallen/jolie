module Typecheck where

open import Function
open import Expr
open import Type
open import Behaviour
open import Variable


data Check (Γ : Ctx) : Behaviour → Set where
  yes : {b : Behaviour} → Check Γ b
  no : {b : Behaviour} → Check Γ b

typecheck_behaviour : (Γ : Ctx) → (b : Behaviour) → Check Γ b
typecheck_behaviour env nil = yes
typecheck_behaviour env (if e b1 maybe_b2) =
  case e of λ
  {
    -- If conditional expression is variable
    (var v) →
      let ctx1 = typecheck_behaviour env b1 in
      {!!}
  ; _ → no
  }
typecheck_behaviour _ _ = no
