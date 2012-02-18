module Code where

open import Function
open import Data.List

open import TypeUniverse
open import Expression
open import Denotation

Shape : Set
Shape = List U

data Instr : Shape → Shape → Set where
  PUSH : ∀ {u s} → el u → Instr s (u ∷ s)
  ADD  : ∀ {s} → Instr (Nat ∷ Nat ∷ s) (Nat ∷ s)

infixr 3 _,,_
data Code : Shape → Shape → Set where
  cnil : ∀ {s} → Code s s
  _,,_ : ∀ {s t u} → Instr s t → Code t u → Code s u

infixr 3 _::_
data Stack : Shape → Set where
  snil : Stack []
  _::_ : ∀ {u s} → el u → Stack s → Stack (u ∷ s)

