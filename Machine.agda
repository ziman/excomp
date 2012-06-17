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
  data Instr : Shape × List U → Shape × List U → Set where
    PUSH : ∀ {u s hs} → el u → Instr (s , hs) (Val u ∷ s , hs)
    ADD : ∀ {s hs} → Instr (Val Nat ∷ Val Nat ∷ s , hs) (Val Nat ∷ s , hs)
    MARK : ∀ {u s hs} → Code (s , hs) (Val u ∷ s , hs) → Instr (s , hs) (Han u ∷ s , u ∷ hs)
    UNMARK : ∀ {u s hs} → Instr (Val u ∷ Han u ∷ s , u ∷ hs) (Val u ∷ s , hs)
    THROW : ∀ {u s hs} → Instr (s , hs) (Val u ∷ s , hs)

  -- Code is an (indexed) list of instructions.
  Code : Shape × List U → Shape × List U → Set
  Code = Star Instr

infixr 3 _::_
infixr 3 _!!_
data Stack : Shape → Set where
  snil : Stack []
  _::_ : ∀ {u s} → el u → Stack s → Stack (Val u ∷ s)
  _!!_ : ∀ {u s hs} → Code (s , hs) (Val u ∷ s , hs) → Stack s → Stack (Han u ∷ s)

data State (r : Shape) : Set where
  ✓[_,_] : ∀ {s hs} → Code (s , hs) (r , []) → Stack s → State r
  ×[] : State r

data Result (r : Shape) : Set where
  Success : Stack r → Result r
  Failure : Result r




