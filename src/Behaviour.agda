module Behaviour where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Vec using (Vec)
open import Data.Product using (_×_)
open import Variable
open import Expr
open import Type


data Output_ex : Set where
  notification : Operation → Location → Expr → Output_ex
  solicitres : Operation → Location → Expr → Variable → Output_ex

data Behaviour : Set

data Input_ex : Set where
  oneway : Operation → Variable → Input_ex
  reqres : Operation → Variable → Variable → Behaviour → Input_ex

data Behaviour where
  input : Input_ex → Behaviour
  output : Output_ex → Behaviour
  if : Expr → Behaviour → Behaviour → Behaviour
  while : Expr → Behaviour → Behaviour
  seq : Behaviour → Behaviour → Behaviour
  par : Behaviour → Behaviour → Behaviour
  assign : Variable → Expr → Behaviour
  nil : Behaviour
  inputchoice : {n : ℕ} → Vec (Input_ex × Behaviour) n → Behaviour
  wait : Channel → Operation → Location → Variable → Behaviour
  exec : Channel → Operation → Variable → Behaviour → Behaviour

