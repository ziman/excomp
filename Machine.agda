module Machine where

open import Function
open import Data.List
open import Data.Sum
open import Data.Maybe
open import Data.Star
open import Data.Product

open import TypeUniverse
open import Expression

-- Stack items.
data Item : Set where
  Val : U → Item
  Han : U → Item

-- Shape of the stack.
Shape : Set
Shape = List Item

mutual
  -- Instructions of the stack machine.
  data Instr : Shape → Shape → Set where
    PUSH : ∀ {u s} → el u → Instr s (Val u ∷ s)
    ADD : ∀ {s} → Instr (Val Nat ∷ Val Nat ∷ s) (Val Nat ∷ s)
    MARK : ∀ {u s} → Code s (Val u ∷ s) → Instr s (Han u ∷ s)
    UNMARK : ∀ {u s} → Instr (Val u ∷ Han u ∷ s) (Val u ∷ s)
    THROW : ∀ {u s} → Instr s (Val u ∷ s)

  -- Code is an (indexed) list of instructions.
  Code : Shape → Shape → Set
  Code = Star Instr

infixr 3 _::_
infixr 3 _!!_
data Stack : Shape → Set where
  snil : Stack []
  _::_ : ∀ {u s} → el u → Stack s → Stack (Val u ∷ s)
  _!!_ : ∀ {u s} → Code s (Val u ∷ s) → Stack s → Stack (Han u ∷ s)

data State (r : Shape) : Set where
  ✓[_,_] : ∀ {s} → Code s r → Stack s → State r
  ×[] : State r

data Result (r : Shape) : Set where
  Success : Stack r → Result r
  Failure : Result r




