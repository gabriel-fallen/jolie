module Type where

open import Level
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; cong₂)
open import Function
open import Data.Nat using (ℕ)
open import Data.Empty
open import Data.String using (String)
open import Data.List using (List)
open import Data.Vec using (Vec)
open import Expr
open import Variable


Operation : Set
Operation = String

Location : Set
Location = String

Channel : Set
Channel = String

data Cardinality : Set where
  oo oi ii : Cardinality

data BasicType : Set where
  bool int double long string raw void : BasicType

data TypeTree : Set

data ChildType : Set where
  child : String → Cardinality → TypeTree → ChildType

data TypeTree where
  leaf : BasicType → TypeTree
  node : BasicType → List ChildType → TypeTree

get-basic : TypeTree → BasicType
get-basic (leaf b) = b
get-basic (node b _) = b

data TypeDecl : Set where
  outNotify : Operation → Location → TypeTree → TypeDecl
  outSolRes : Operation → Location → TypeTree → TypeTree → TypeDecl
  inOneWay : Operation → TypeTree → TypeDecl
  inReqRes : Operation → TypeTree → TypeTree → TypeDecl
  var : Variable → TypeTree → TypeDecl
  empty : TypeDecl
  pair : TypeDecl → TypeDecl → TypeDecl

data _⊆_ : TypeTree → TypeTree → Set where
  sub : {T₁ T₂ : TypeTree} → T₁ ⊆ T₂

Ctx : ℕ → Set
Ctx = Vec TypeDecl
