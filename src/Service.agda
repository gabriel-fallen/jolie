module Service where

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.String using (String)
open import Data.Product using (_×_)
open import Type
open import Behaviour
open import Queue
open import Variable


Message : Set
Message = Channel × Operation × String

MessageQueue : Set
MessageQueue = Queue Message

data Process : Set where
  _∙_∙_ : Behaviour → List Variable → MessageQueue → Process
  nil : Process
  _||_ : Process → Process → Process

data AliasingFunction : Set where

Deployment : {m : ℕ} → Set
Deployment {m} = AliasingFunction × Ctx m

data Service : Set where
  service : {m : ℕ} → Behaviour → Deployment {m} → Process → Service
