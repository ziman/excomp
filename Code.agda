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
data Code : Shape → Shape → Set where
  cnil : ∀ {s} → Code s s
  _,,_ : ∀ {s t u} → Instr s t → Code t u → Code s u

infixr 5 _::_
data Stack : Shape → Set where
  ∅ : Stack []
  _::_ : ∀ {u s} → el u → Stack s → Stack (u ∷ s)

infixr 6 _⊕_
_⊕_ : ∀ {s t u} → Code s t → Code t u → Code s u
_⊕_ cnil      cs = cs
_⊕_ (i ,, is) cs = i ,, (is ⊕ cs)
