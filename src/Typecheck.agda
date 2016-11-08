module Typecheck where

import Data.List as List
import Data.Vec.Equality as VecEq
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Data.Nat using (ℕ; _+_)
open import Data.Vec using (Vec; _∈_; zip)
open import Expr
open import Type
open import Behaviour
open import Variable


data _⊢_of_ {n : ℕ} (Γ : Ctx n) : Variable → TypeTree → Set where
  var-t : {s : Variable} {b : TypeTree} 
        → Γ ⊢ s of b

data _⊢ₑ_of_ {n : ℕ} (Γ : Ctx n) : Expr → TypeTree → Set where
  expr-t : {s : Expr} {b : TypeTree}
         → Γ ⊢ₑ s of b

data _⊢_▹_ {n m : ℕ} (Γ : Ctx n) : Behaviour → (Γ₁ : Ctx m) → Set where 
  t-nil : {Γ₁ : Ctx m}
        → n ≡ m
        --------------
        → Γ ⊢ nil ▹ Γ₁
          
  t-if : {Γ₁ : Ctx m} {b1 b2 : Behaviour} {e : Variable}
       → Γ ⊢ e of (leaf bool) -- Γ ⊢ e : bool
       → Γ ⊢ b1 ▹ Γ₁
       → Γ ⊢ b2 ▹ Γ₁
       ---------------------------
       → Γ ⊢ if (var e) b1 b2 ▹ Γ₁
          
  t-while : {Γ₁ : Ctx m} {b : Behaviour} {e : Variable}
          → Γ ⊢ e of (leaf bool)
          → Γ ⊢ b ▹ Γ₁
          --------------------------
          → Γ ⊢ while (var e) b ▹ Γ₁
          
  t-choice : {Γ₁ : Ctx m} {k n : ℕ}  {η : Input_ex} {inputs : Vec Input_ex n}
             {b : Behaviour} {behaviours : Vec Behaviour n}
           → η ∈ inputs
           → b ∈ behaviours
           → Γ ⊢ seq (input η) b ▹ Γ₁
           ----------------------------------------------
           → Γ ⊢ inputchoice (zip inputs behaviours) ▹ Γ₁

  t-par : {k k₁ p p₁ : ℕ} {b1 b2 : Behaviour}
          {Γ₁ : Ctx k} {Γ₁' : Ctx k₁} {Γ₂ : Ctx p} {Γ₂' : Ctx p₁} {Γ' : Ctx m}
        → Γ₁ ⊢ b1 ▹ Γ₁'
        → Γ₂ ⊢ b2 ▹ Γ₂'
        → intersect-roots (roots Γ₁') (roots Γ₂') ≡ List.[]
        -- TODO: maybe it's not enough to express that Γ = Γ₁, Γ₂ and Γ' = Γ₁', Γ₂' - disjoint unions
        --------------------
        → Γ ⊢ par b1 b2 ▹ Γ'

  t-seq : {k : ℕ} {Γ₁ : Ctx k} {Γ₂ : Ctx m} {b1 b2 : Behaviour}
        → Γ ⊢ b1 ▹ Γ₁
        → Γ₁ ⊢ b2 ▹ Γ₂
        --------------------
        → Γ ⊢ seq b1 b2 ▹ Γ₂

  t-notification : {k : ℕ} {Γ₁ : Ctx m} {o : Operation} {l : Location} {e : Variable} {T₀ Tₑ : TypeTree}
                 → (outNotify o l T₀) ∈ Γ
                 → Γ ⊢ e of Tₑ
                 → Tₑ ⊆ T₀
                 -------------------------------------------
                 → n ≡ m
                 → Γ ⊢ output (notification o l (var e)) ▹ Γ₁

  t-assign-new : {Γ₁ : Ctx m} {x : Variable} {e : Expr} {T₀ : TypeTree} {Tₓ : TypeTree}
               → Γ ⊢ₑ e of T₀ -- Γ ⊢ e : bool
               → ¬ (var x Tₓ ∈ Γ) -- x ∉ Γ
               ---------------------
               → Γ ⊢ assign x e ▹ upd Γ x (bt Tₑ)
