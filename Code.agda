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

infixr 5 _,,_
data InstrSeq : Shape → Shape → Set where
  inil : ∀ {s} → InstrSeq s s
  _,,_ : ∀ {s t u} → Instr s t → InstrSeq t u → InstrSeq s u

infixr 5 _::_
data Stack : Shape → Set where
  ∅ : Stack []
  _::_ : ∀ {u s} → el u → Stack s → Stack (u ∷ s)

-- [Code s t r] represents code transforming a stack of shape [s]
-- into a stack of shape [t], leaving the total result type open.
Code : Shape → Shape → Set
Code s t = {r : Shape} → InstrSeq t r → InstrSeq s r
