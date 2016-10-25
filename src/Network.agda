module Network where

open import Type
open import Service


data Network : Set where
  [_]_ : Service → Location → Network
  νr : Network → Network
  _||_ : Network → Network → Network
  nil : Network
