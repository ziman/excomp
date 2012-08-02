module Code where

open import Data.List
open import Data.Star

open import TypeUniverse

-- Shape of the stack.
Shape : Set
Shape = List U

-- Instructions of the stack machine.
data Instr : Shape → Shape → Set where
  PUSH : ∀ {u s} → el u → Instr s (u ∷ s)
  ADD  : ∀ {s} → Instr (nat ∷ nat ∷ s) (nat ∷ s)

-- Code is an (indexed) list of instructions.
Code : Shape → Shape → Set
Code = Star Instr

-- Stack is a shape-indexed... well, stack.
infixr 5 _:-:_
data Stack : Shape → Set where
  snil : Stack []
  _:-:_ : ∀ {u s} → el u → Stack s → Stack (u ∷ s)

