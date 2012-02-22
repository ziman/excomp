module Code where

open import Function
open import Data.List
open import Data.Sum

open import TypeUniverse
open import Expression

-- Stack items.
data Item : Set where
  Val : U → Item
  Han : U → Item

-- Shape of the stack.
Shape : Set
Shape = List Item

unwind : (s : Shape) → Shape
unwind []           = []
unwind (Val _ ∷ xs) = unwind xs
unwind (Han _ ∷ xs) = xs

mutual
  -- Instructions of the stack machine.
  data Instr : Shape → Shape → Set where
    PUSH   : ∀ {u s} → el u → Instr s (Val u ∷ s)
    ADD    : ∀ {s} → Instr (Val Nat ∷ Val Nat ∷ s) (Val Nat ∷ s)
    MARK   : ∀ {u s} → Code s (Val u ∷ s) → Instr s (Han u ∷ s) 
    UNMARK : ∀ {u s} → Instr (Han u ∷ s) s
    THROW  : ∀ {s} → Instr s (unwind s)

  -- Code is an (indexed) list of instructions.
  infixr 5 _,,_
  data Code : Shape → Shape → Set where
    cnil : ∀ {s} → Code s s
    _,,_ : ∀ {s t u} → Instr s t → Code t u → Code s u

-- Stack is a shape-indexed... well, stack.
infixr 5 _::_
infixr 5 _!!_
data Stack : Shape → Set where
  snil : Stack []
  _::_ : ∀ {u s} → el u → Stack s → Stack (Val u ∷ s)
  _!!_ : ∀ {u s} → Code s (Val u ∷ s) → Stack s → Stack (Han u ∷ s)

-- Code concatenation.
infixr 6 _⊕_
_⊕_ : ∀ {s t u} → Code s t → Code t u → Code s u
_⊕_ cnil      cs = cs
_⊕_ (i ,, is) cs = i ,, (is ⊕ cs)
