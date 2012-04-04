module Execution.Utils where

open import Data.Nat
open import Data.List
open import Data.Maybe

open import TypeUniverse
open import Code

unwindHnd : Shape → ℕ → Maybe U
unwindHnd (Han u ∷ xs) zero    = just u
unwindHnd (Han _ ∷ xs) (suc n) = unwindHnd xs n
unwindHnd (Val _ ∷ xs) n       = unwindHnd xs n
unwindHnd []           _       = nothing

unwindShape : Shape → ℕ → Shape
unwindShape (Han _ ∷ xs) zero    = xs
unwindShape (Han _ ∷ xs) (suc n) = unwindShape xs n
unwindShape (Val _ ∷ xs) n       = unwindShape xs n
unwindShape []           _       = []

data Resume (s : Shape) : Maybe U → Set where
  Okay : ∀ {u} → Code s (Val u ∷ s) → Stack s → Resume s (just u)
  Fail : Resume s nothing

unwindStack : ∀ {s} → Stack s → (n : ℕ) → Resume (unwindShape s n) (unwindHnd s n)
unwindStack (h !! xs) zero    = Okay h xs
unwindStack (_ !! xs) (suc n) = unwindStack xs n
unwindStack (_ :: xs) n       = unwindStack xs n
unwindStack snil      _       = Fail
