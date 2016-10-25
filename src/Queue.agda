module Queue where

open import Data.List using (List)


data Queue (A : Set) : Set where
  nil : Queue A
  cons : List A → List A → Queue A
