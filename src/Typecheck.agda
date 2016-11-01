module Typecheck where

import Relation.Binary.PropositionalEquality as PropEq
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (if_then_else_)
open import Data.Product using (_,_)
open import Function
open import Expr
open import Type
open import Behaviour
open import Variable


type_of_value : Value → BasicType
type_of_value (Value.string _) = Type.string
type_of_value (Value.int _) = Type.int
type_of_value (Value.bool _) = Type.bool
type_of_value (Value.double _) = Type.double
type_of_value (Value.long _) = Type.long

type_of_var : Variable → Maybe BasicType
type_of_var (leaf _ v) = just $ type_of_value v
type_of_var _ = nothing

data Check (Γ : Ctx) : Behaviour → Set where
  yes : {b : Behaviour} → Check Γ b
  no : {b : Behaviour} → Check Γ b

typecheck_behaviour : (Γ : Ctx) → (b : Behaviour) → Check Γ b
typecheck_behaviour ctx nil = yes
typecheck_behaviour ctx (if e b1 b2) =
  case e of λ
  {
    -- If conditional expression is variable
    (var v) →
      let ctx1 = typecheck_behaviour ctx b1 in
      case (type_of_var v) of λ
      -- If e : bool
      { (just bool) →
        let ctx2 = typecheck_behaviour ctx b2 in
        {!!}
      ; _ → no
      }
      --case ()
  ; _ → no
  }
typecheck_behaviour _ _ = no
