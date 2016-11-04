module Type where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; cong₂)
open import Function using (_∘_)
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

module BasicTypeEq where
  _≟_ : Decidable {A = BasicType} _≡_
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

data TypeTree : Set

data ChildType : Set where
  child : String → Cardinality → TypeTree → ChildType

data TypeTree where
  leaf : BasicType → TypeTree
  node : BasicType → List ChildType → TypeTree

get-basic : TypeTree → BasicType
get-basic (leaf b) = b
get-basic (node b _) = b

module TypeTreeEq where
  _≟_ : Decidable {A = TypeTree} _≡_
  (leaf b1) ≟ (leaf b2) with BasicTypeEq._≟_ b1 b2
  ... | yes b1≡b2 = yes (cong leaf b1≡b2)
  ... | no b1≢b2 = no {!!} -- ¬ leaf b1 ≡ leaf b2
  (node b1 cts) ≟ (node b2 cts') = {!!}
  (leaf _) ≟ (node _ _) = no λ ()
  (node _ _) ≟ (leaf _) = no λ ()

data TypeDecl : Set where
  outNotify : Operation → Location → TypeTree → TypeDecl
  outSolRes : Operation → Location → TypeTree → TypeTree → TypeDecl
  inOneWay : Operation → TypeTree → TypeDecl
  inReqRes : Operation → TypeTree → TypeTree → TypeDecl
  var : Variable → TypeTree → TypeDecl
  empty : TypeDecl
  pair : TypeDecl → TypeDecl → TypeDecl

module TypeDeclEq where
  _≟_ : Decidable {A = TypeDecl} _≡_
  (outNotify o1 l1 t1) ≟ (outNotify o2 l2 t2) = {!!}
  (outSolRes o1 l1 t1 t1') ≟ (outSolRes o2 l2 t2 t2') = {!!}
  (inOneWay o1 t1) ≟ (inOneWay o2 t2) = {!!}
  (inReqRes o1 t1 t1') ≟ (inReqRes o2 t2 t2') = {!!}
  (var v1 t1) ≟ (var v2 t2) = {!!}
  (pair t1 t1') ≟ (pair t2 t2') = {!!}
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


Ctx : ℕ → Set
Ctx = Vec TypeDecl
