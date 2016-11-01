module Type where

open import Data.String using (String)
open import Data.List using (List)
open import Expr
open import Variable


Operation : Set
Operation = String

Location : Set
Location = String

Channel : Set
Channel = String

data Cardinality : Set where
  oo : Cardinality
  oi : Cardinality
  ii : Cardinality

data BasicType : Set where
  bool : BasicType
  int : BasicType
  double : BasicType
  long : BasicType
  string : BasicType
  raw : BasicType
  void : BasicType

data TypeTree : Set

data ChildType : Set where
  child : String → Cardinality → TypeTree → ChildType

data TypeTree where
  leaf : BasicType → TypeTree
  node : BasicType → List ChildType → TypeTree

data TypeDecl : Set where
  outNotify : Operation → Location → TypeTree → TypeDecl
  outSolRes : Operation → Location → TypeTree → TypeTree → TypeDecl
  inOneWay : Operation → TypeTree → TypeDecl
  inReqRes : Operation → TypeTree → TypeTree → TypeDecl
  var : Variable → TypeTree → TypeDecl
  empty : TypeDecl
  pair : TypeDecl → TypeDecl → TypeDecl

Ctx : Set
Ctx = List TypeDecl
