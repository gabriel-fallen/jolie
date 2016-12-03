
module Typecheck where

import Data.List as List
import Data.Vec.Equality as VecEq
open import Relation.Nullary using (¬_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Vec using (Vec; _∈_; zip; _∷_)
open import Expr
open import Type
open import Behaviour
open import Variable


data _⊢_of_ {n : ℕ} (Γ : Ctx n) : Variable → Type → Set where
  var-t : {s : Variable} {b : Type}
        → Γ ⊢ s of b

data _⊢ₑ_of_ {n : ℕ} (Γ : Ctx n) : Expr → Type → Set where
  expr-t : {s : Expr} {b : Type}
         → Γ ⊢ₑ s of b

data _⊢B_▹_ {n m : ℕ} (Γ : Ctx n) : Behaviour → (Γ₁ : Ctx m) → Set where 
  t-nil : {Γ₁ : Ctx m}
        → n ≡ m
        --------------
        → Γ ⊢B nil ▹ Γ₁
          
  t-if : {Γ₁ : Ctx m} {b1 b2 : Behaviour} {e : Variable}
       → Γ ⊢ e of bool -- Γ ⊢ e : bool
       → Γ ⊢B b1 ▹ Γ₁
       → Γ ⊢B b2 ▹ Γ₁
       ---------------------------
       → Γ ⊢B if (var e) b1 b2 ▹ Γ₁
          
  t-while : {Γ₁ : Ctx m} {b : Behaviour} {e : Variable}
          → Γ ⊢ e of bool
          → Γ ⊢B b ▹ Γ₁
          --------------------------
          → Γ ⊢B while (var e) b ▹ Γ₁
          
  t-choice : {Γ₁ : Ctx m} {k n : ℕ}  {η : Input_ex} {inputs : Vec Input_ex n}
             {b : Behaviour} {behaviours : Vec Behaviour n}
           → η ∈ inputs
           → b ∈ behaviours
           → Γ ⊢B seq (input η) b ▹ Γ₁
           ----------------------------------------------
           → Γ ⊢B inputchoice (zip inputs behaviours) ▹ Γ₁

  t-par : {k k₁ p p₁ : ℕ} {b1 b2 : Behaviour}
          {Γ₁ : Ctx k} {Γ₁' : Ctx k₁} {Γ₂ : Ctx p} {Γ₂' : Ctx p₁} {Γ' : Ctx m}
        → Γ₁ ⊢B b1 ▹ Γ₁'
        → Γ₂ ⊢B b2 ▹ Γ₂'
        -- TODO: maybe it's not enough to express that Γ = Γ₁, Γ₂ and Γ' = Γ₁', Γ₂' - disjoint unions
        --------------------
        → Γ ⊢B par b1 b2 ▹ Γ'

  t-seq : {k : ℕ} {Γ₁ : Ctx k} {Γ₂ : Ctx m} {b1 b2 : Behaviour}
        → Γ ⊢B b1 ▹ Γ₁
        → Γ₁ ⊢B b2 ▹ Γ₂
        --------------------
        → Γ ⊢B seq b1 b2 ▹ Γ₂

  t-notification : {k : ℕ} {Γ₁ : Ctx m} {o : Operation} {l : Location} {e : Variable} {T₀ Tₑ : Type}
                 → (outNotify o l T₀) ∈ Γ
                 → Γ ⊢ e of Tₑ
                 → Tₑ ⊆ T₀
                 → n ≡ m
                 -------------------------------------------
                 → Γ ⊢B output (notification o l (var e)) ▹ Γ₁

  t-assign-new : {Γ₁ : Ctx m} {x : Variable} {e : Expr} {Tₓ Tₑ : Type}
               → Γ ⊢ₑ e of Tₑ -- Γ ⊢ e : bool
               → ¬ (var x Tₓ ∈ Γ) -- x ∉ Γ
               → (var x Tₑ) ∈ Γ₁
               ---------------------
               → Γ ⊢B assign x e ▹ Γ₁

  t-assign-exists : {Γ₁ : Ctx m} {x : Variable} {e : Expr} {Tₓ Tₑ : Type}
                  → Γ ⊢ₑ e of Tₑ
                  → (var x Tₓ) ∈ Γ
                  → Tₑ ≡ Tₓ
                  → n ≡ m -- TODO Γ ≡ Γ₁
                  ---------------------
                  → Γ ⊢B assign x e ▹ Γ₁

  t-oneway-new : {Γ₁ : Ctx m} {Tₓ Tᵢ : Type} {o : Operation} {x : Variable}
               → (inOneWay o Tᵢ) ∈ Γ
               → ¬ ((var x Tₓ) ∈ Γ)
               → (var x Tᵢ) ∈ Γ₁
               -------------------------------
               → Γ ⊢B (input (oneway o x)) ▹ Γ₁

  t-oneway-exists : {Γ₁ : Ctx m} {Tₓ Tᵢ : Type} {o : Operation} {x : Variable}
                  → (inOneWay o Tᵢ) ∈ Γ
                  → ((var x Tₓ) ∈ Γ)
                  → Tᵢ ⊆ Tₓ
                  → n ≡ m -- TODO Γ ≡ Γ₁
                  --------------------------------
                  → Γ ⊢B (input (oneway o x)) ▹ Γ₁

  t-solresp-new : {Γ₁ : Ctx m} {o : Operation} {l : Location} {Tₒ Tᵢ Tₑ Tₓ : Type} {e : Expr} {x : Variable}
                → (outSolRes o l Tₒ Tᵢ) ∈ Γ
                → Tₑ ⊆ Tₒ
                → ¬ (var x Tₓ ∈ Γ)
                → (var x Tᵢ) ∈ Γ₁
                -----------------------------------------
                → Γ ⊢B (output (solicitres o l e x)) ▹ Γ₁

  t-solresp-exists : {Γ₁ : Ctx m} {o : Operation} {l : Location} {Tₒ Tᵢ Tₑ Tₓ : Type} {e : Expr} {x : Variable}
                   → (outSolRes o l Tₒ Tᵢ) ∈ Γ
                   → Tₑ ⊆ Tₒ
                   → (var x Tₓ) ∈ Γ
                   → Tᵢ ⊆ Tₓ
                   → n ≡ m -- TODO Γ ≡ Γ₁
                   -----------------------------------------
                   → Γ ⊢B (output (solicitres o l e x)) ▹ Γ₁

  t-reqresp-new : {p : ℕ} {Γₓ : Ctx p} {Γ₁ : Ctx m} {o : Operation} {Tᵢ Tₒ Tₓ Tₐ : Type} {x a : Variable} {b : Behaviour}
                → (inReqRes o Tᵢ Tₒ) ∈ Γ
                → ¬ (var x Tₓ ∈ Γ)
                → (var x Tₓ) ∈ Γₓ
                → Γₓ ⊢B b ▹ Γ₁
                → (var a Tₐ) ∈ Γ₁
                → Tₐ ⊆ Tₒ
                -----------------------------------
                → Γ ⊢B (input (reqres o x a b)) ▹ Γ₁

  t-reqresp-exists : {Γ₁ : Ctx m} {o : Operation} {Tᵢ Tₒ Tₓ Tₐ : Type} {b : Behaviour} {x a : Variable}
                   → (inReqRes o Tᵢ Tₒ) ∈ Γ
                   → (var x Tₓ) ∈ Γ
                   → Tᵢ ⊆ Tₓ
                   → Γ ⊢B b ▹ Γ₁
                   → (var a Tₐ) ∈ Γ₁
                   → Tₐ ⊆ Tₒ
                   ------------------------------------
                   → Γ ⊢B (input (reqres o x a b)) ▹ Γ₁


check-B : {n m : ℕ} {Γ₁ : Ctx m} → (Γ : Ctx n) → (B : Behaviour) → Dec (Γ ⊢B B ▹ Γ₁)
check-B = {!!}
