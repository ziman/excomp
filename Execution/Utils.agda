module Execution.Utils where

open import Data.Nat
open import Data.List
open import Data.Maybe

open import TypeUniverse
open import Code

data Resume (s : Shape) : Maybe U → Set where
  Okay : ∀ {u} → (c : Code s (Val u ∷ s)) → (st : Stack s) → Resume s (just u)
  Fail : Resume s nothing

