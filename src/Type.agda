module Type where

import Data.Vec.Equality as VecEq
open import Level
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function
open import Data.Nat using (ℕ) renaming (_≟_ to _≟-Nat_)
open import Data.Empty
open import Data.String using (String) renaming (_≟_ to _≟-String_)
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

module TypeEq where
  _≟_ : Decidable {A = Type} _≡_
  bool ≟ bool = yes refl
  int ≟ int = yes refl
  double ≟ double = yes refl
  long ≟ long = yes refl
  string ≟ string = yes refl
  raw ≟ raw = yes refl
  void ≟ void = yes refl
  bool ≟ int = no λ()
  bool ≟ double = no λ()
  bool ≟ long = no λ()
  bool ≟ string = no λ()
  bool ≟ raw = no λ()
  bool ≟ void = no λ()
  int ≟ bool = no λ()
  int ≟ double = no λ()
  int ≟ long = no λ()
  int ≟ string = no λ()
  int ≟ raw = no λ()
  int ≟ void = no λ()
  double ≟ bool = no λ()
  double ≟ int = no λ()
  double ≟ long = no λ()
  double ≟ string = no λ()
  double ≟ raw = no λ()
  double ≟ void = no λ()
  long ≟ bool = no λ()
  long ≟ int = no λ()
  long ≟ double = no λ()
  long ≟ string = no λ()
  long ≟ raw = no λ()
  long ≟ void = no λ()
  string ≟ bool = no λ()
  string ≟ int = no λ()
  string ≟ double = no λ()
  string ≟ long = no λ()
  string ≟ raw = no λ()
  string ≟ void = no λ()
  raw ≟ bool = no λ()
  raw ≟ int = no λ()
  raw ≟ double = no λ()
  raw ≟ long = no λ()
  raw ≟ string = no λ()
  raw ≟ void = no λ()
  void ≟ bool = no λ()
  void ≟ int = no λ()
  void ≟ double = no λ()
  void ≟ long = no λ()
  void ≟ string = no λ()
  void ≟ raw = no λ()

data TypeDecl : Set where
  outNotify : Operation → Location → Type → TypeDecl
  outSolRes : Operation → Location → Type → Type → TypeDecl
  inOneWay : Operation → Type → TypeDecl
  inReqRes : Operation → Type → Type → TypeDecl
  var : Variable → Type → TypeDecl
  empty : TypeDecl
  pair : TypeDecl → TypeDecl → TypeDecl

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v m n} → x ≡ y → u ≡ v → m ≡ n → f x u m ≡ f y v n
cong₃ f refl refl refl = refl

cong₄ : ∀ {a b c d e} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
        (f : A → B → C → D → E) {x y u v m n k l} → x ≡ y → u ≡ v → m ≡ n → k ≡ l → f x u m k ≡ f y v n l
cong₄ f refl refl refl refl = refl

module TypeDeclEq where
  _≟_ : Decidable {A = TypeDecl} _≡_
  (outNotify o1 l1 t1) ≟ (outNotify o2 l2 t2) with o1 ≟-String o2 | l1 ≟-String l2 | t1 TypeEq.≟ t2
  ... | yes o | yes l | yes t = yes (cong₃ outNotify o l t)
  ... | no ¬p | _ | _ = no (λ { refl → ¬p refl})
  ... | _ | no ¬p | _ = no (λ { refl → ¬p refl})
  ... | _ | _ | no ¬p = no (λ { refl → ¬p refl})
  (outSolRes o1 l1 t1 t1') ≟ (outSolRes o2 l2 t2 t2') with o1 ≟-String o2 | l1 ≟-String l2 | t1 TypeEq.≟ t2 | t1' TypeEq.≟ t2'
  ... | yes o | yes l | yes t | yes t' = yes (cong₄ outSolRes o l t t')
  ... | no ¬p | _ | _ | _ = no (λ { refl → ¬p refl})
  ... | _ | no ¬p | _ | _ = no (λ { refl → ¬p refl})
  ... | _ | _ | no ¬p | _ = no (λ { refl → ¬p refl})
  ... | _ | _ | _ | no ¬p = no (λ { refl → ¬p refl})
  (inOneWay o1 t1) ≟ (inOneWay o2 t2) with o1 ≟-String o2 | t1 TypeEq.≟ t2
  ... | yes o | yes t = yes (cong₂ inOneWay o t)
  ... | no ¬p | _ = no (λ { refl → ¬p refl})
  ... | _ | no ¬p = no (λ { refl → ¬p refl})
  (inReqRes o1 t1 t1') ≟ (inReqRes o2 t2 t2') with o1 ≟-String o2 | t1 TypeEq.≟ t2 | t1' TypeEq.≟ t2'
  ... | yes o | yes l | yes t = yes (cong₃ inReqRes o l t)
  ... | no ¬p | _ | _ = no (λ { refl → ¬p refl})
  ... | _ | no ¬p | _ = no (λ { refl → ¬p refl})
  ... | _ | _ | no ¬p = no (λ { refl → ¬p refl})
  (var v1 t1) ≟ (var v2 t2) with v1 ≟-Nat v2 | t1 TypeEq.≟ t2
  ... | yes v | yes t = yes (cong₂ var v t)
  ... | no ¬p | _ = no (λ { refl → ¬p refl})
  ... | _ | no ¬p = no (λ { refl → ¬p refl})
  (pair t1 t1') ≟ (pair t2 t2') with t1 ≟ t2 | t1' ≟ t2'
  ... | yes t | yes t' = yes (cong₂ pair t t')
  ... | no ¬p | _ = no (λ { refl → ¬p refl})
  ... | _ | no ¬p = no (λ { refl → ¬p refl})
  empty ≟ empty = yes refl
  empty ≟ (outNotify _ _ _) = no λ()
  empty ≟ (outSolRes _ _ _ _) = no λ()
  empty ≟ (inOneWay _ _) = no λ()
  empty ≟ (inReqRes _ _ _) = no λ()
  empty ≟ (var _ _) = no λ()
  empty ≟ (pair _ _) = no λ()
  (outNotify _ _ _) ≟ (outSolRes _ _ _ _) = no λ()
  (outNotify _ _ _) ≟ (inOneWay _ _) = no λ()
  (outNotify _ _ _) ≟ (inReqRes _ _ _) = no λ()
  (outNotify _ _ _) ≟ (var _ _) = no λ()
  (outNotify _ _ _) ≟ empty = no λ()
  (outNotify _ _ _) ≟ (pair _ _) = no λ()
  (outSolRes _ _ _ _) ≟ (outNotify _ _ _) = no λ()
  (outSolRes _ _ _ _) ≟ (inOneWay _ _) = no λ()
  (outSolRes _ _ _ _) ≟ (inReqRes _ _ _) = no λ()
  (outSolRes _ _ _ _) ≟ (var _ _) = no λ()
  (outSolRes _ _ _ _) ≟ empty = no λ()
  (outSolRes _ _ _ _) ≟ (pair _ _) = no λ()
  (inOneWay _ _) ≟ (outNotify _ _ _) = no λ()
  (inOneWay _ _) ≟ (outSolRes _ _ _ _) = no λ()
  (inOneWay _ _) ≟ (inReqRes _ _ _) = no λ()
  (inOneWay _ _) ≟ (var _ _) = no λ()
  (inOneWay _ _) ≟ empty = no λ()
  (inOneWay _ _) ≟ (pair _ _) = no λ()
  (inReqRes _ _ _) ≟ (outNotify _ _ _) = no λ()
  (inReqRes _ _ _) ≟ (outSolRes _ _ _ _) = no λ()
  (inReqRes _ _ _) ≟ (inOneWay _ _) = no λ()
  (inReqRes _ _ _) ≟ (var _ _) = no λ()
  (inReqRes _ _ _) ≟ empty = no λ()
  (inReqRes _ _ _) ≟ (pair _ _) = no λ()
  (var _ _) ≟ (outNotify _ _ _) = no λ()
  (var _ _) ≟ (outSolRes _ _ _ _) = no λ()
  (var _ _) ≟ (inOneWay _ _) = no λ()
  (var _ _) ≟ (inReqRes _ _ _) = no λ()
  (var _ _) ≟ empty = no λ()
  (var _ _) ≟ (pair _ _) = no λ()
  (pair _ _) ≟ (outNotify _ _ _) = no λ()
  (pair _ _) ≟ (outSolRes _ _ _ _) = no λ()
  (pair _ _) ≟ (inOneWay _ _) = no λ()
  (pair _ _) ≟ (inReqRes _ _ _) = no λ()
  (pair _ _) ≟ (var _ _) = no λ()
  (pair _ _) ≟ empty = no λ()
  
  decSetoid : DecSetoid _ _
  decSetoid = PropEq.decSetoid _≟_

data _⊆_ : Type → Type → Set where
  sub : {T₁ T₂ : Type} → T₁ ⊆ T₂

Ctx : ℕ → Set
Ctx = Vec TypeDecl

module CtxEq = VecEq.DecidableEquality TypeDeclEq.decSetoid
