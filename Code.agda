module Code where

open import Function
open import Data.List
open import Data.Star

open import TypeUniverse
open import Expression
open import Denotation

-- Shape of the stack.
Shape : Set
Shape = List U

-- Instructions of the stack machine.
data Instr : Shape → Shape → Set where
  PUSH : ∀ {u s} → el u → Instr s (u ∷ s)
  ADD  : ∀ {s} → Instr (Nat ∷ Nat ∷ s) (Nat ∷ s)

-- Code is an (indexed) list of instructions.
Code : Shape → Shape → Set
Code = Star Instr

-- Stack is a shape-indexed... well, stack.
infixr 5 _:-:_
data Stack : Shape → Set where
  ∅ : Stack []
  _:-:_ : ∀ {u s} → el u → Stack s → Stack (u ∷ s)

