module Variable where

open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe)
open import Data.List using (List)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)


Variable : Set
Variable = ℕ

data Value : Set where
  string : String → Value
  int : ℤ → Value
  bool : Bool → Value
  double : ℤ × ℤ → Value
  long : ℤ → Value
  void : Value
