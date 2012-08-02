module Code where

open import Data.List
open import Data.Star

open import TypeUniverse

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
    ADD : ∀ {s} → Instr (Val nat ∷ Val nat ∷ s) (Val nat ∷ s)
    MARK : ∀ {u s} → Instr s (Han u ∷ s)
    UNMARK : ∀ {u s} → Code s (Val u ∷ s) → Instr (Val u ∷ Han u ∷ s) (Val u ∷ s)
    THROW : ∀ {u s} → Instr s (Val u ∷ s)

  -- Code is an (indexed) list of instructions.
  Code : Shape → Shape → Set
  Code = Star Instr

infixr 50 _::_
infixr 50 ■!!_
data Stack : Shape → Set where
  snil : Stack []
  _::_ : ∀ {u s} → el u → Stack s → Stack (Val u ∷ s)
  ■!!_ : ∀ {u s} → Stack s → Stack (Han u ∷ s)

