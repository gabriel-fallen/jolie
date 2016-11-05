module Variable where

open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe)
open import Data.List using (List)
open import Data.Bool using (Bool)


Name : Set
Name = String

data Value : Set where
  string : String → Value
  int : ℤ → Value
  bool : Bool → Value
  double : ℤ × ℤ → Value
  long : ℤ → Value

data Variable : Set where
  leaf : Name → Value → Variable
  node : Name → Maybe Value → List Variable → Variable

root : Variable → Name
root (leaf n _) = n
root (node n _ _) = n
