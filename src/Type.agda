module Type where

open import Level
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function
open import Data.Nat using (ℕ)
open import Data.Empty
open import Data.String using (String)
open import Data.List using (List; filter)
open import Data.Vec using (Vec; toList)
open import Expr
open import Variable


Operation : Set
Operation = String

Location : Set
Location = String

Channel : Set
Channel = String

data Type : Set where
  bool int double long string raw void : Type

data TypeDecl : Set where
  outNotify : Operation → Location → Type → TypeDecl
  outSolRes : Operation → Location → Type → Type → TypeDecl
  inOneWay : Operation → Type → TypeDecl
  inReqRes : Operation → Type → Type → TypeDecl
  var : Variable → Type → TypeDecl
  empty : TypeDecl
  pair : TypeDecl → TypeDecl → TypeDecl

data _⊆_ : Type → Type → Set where
  sub : {T₁ T₂ : Type} → T₁ ⊆ T₂

Ctx : ℕ → Set
Ctx = Vec TypeDecl
