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

mutual
  -- Instructions of the stack machine.
  data Instr : Shape → Shape → Set where
    PUSH   : ∀ {u s} → el u → Instr s (Val u ∷ s)
    ADD    : ∀ {s} → Instr (Val Nat ∷ Val Nat ∷ s) (Val Nat ∷ s)
    MARK   : ∀ {u s} → Code s (Val u ∷ s) → Instr s (Han u ∷ s) 
    UNMARK : ∀ {u s} → Instr (Val u ∷ Han u ∷ s) (Val u ∷ s)
    THROW  : ∀ {u s} → Instr s (Val u ∷ s)

  -- Code is an (indexed) list of instructions.
  infixr 5 _,,_
  data Code : Shape → Shape → Set where
    cnil : ∀ {s} → Code s s
    _,,_ : ∀ {s t u} → Instr s t → Code t u → Code s u

-- Stack w s is the type of stacks where:
-- * `s' is the current shape of the stack
-- * `w' is the stack (cons-list) of "throw resume-points",
--   where a "resume-point" is a stack shape where execution
--   would reinstate if we threw an exception right now.
infixr 5 _::_
infixr 5 _!!_
data Stack : List Shape → Shape → Set where
  snil : Stack [] []
  _::_ : ∀ {u w s} → el u → Stack w s → Stack w (Val u ∷ s)
  _!!_ : ∀ {u w s} → Code s (Val u ∷ s) → Stack w s → Stack ((Val u ∷ s) ∷ w) (Han u ∷ s)

-- Code concatenation.
infixr 6 _⊕_
_⊕_ : ∀ {s t u} → Code s t → Code t u → Code s u
_⊕_ cnil      cs = cs
_⊕_ (i ,, is) cs = i ,, (is ⊕ cs)
