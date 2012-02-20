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

data Marked : Shape → Set where
  Here  : ∀ {u s} → Marked (Han u ∷ s)
  Later : ∀ {x s} → Marked s → Marked (x ∷ s)

unwind : (s : Shape) → Marked s → Shape
unwind (_     ∷ xs) (Later pf) = unwind xs pf
unwind (Han _ ∷ xs) Here       = xs
unwind []           ()

-- Instructions of the stack machine.
data Instr : Shape → Shape → Set where
  PUSH  : ∀ {u s} → el u → Instr s (Val u ∷ s)
  ADD   : ∀ {s} → Instr (Val Nat ∷ Val Nat ∷ s) (Val Nat ∷ s)
  MARK  : ∀ {u s} → Exp u → Instr s (Han u ∷ s) 
  THROW : ∀ {s} → (pf : Marked s) → Instr s (unwind s pf)

-- Code is an (indexed) list of instructions.
infixr 5 _,,_
data Code : Shape → Shape → Set where
  cnil : ∀ {s} → Code s s
  _,,_ : ∀ {s t u} → Instr s t → Code t u → Code s u

-- Stack is a shape-indexed... well, stack.
infixr 5 _::_
infixr 5 _!!_
data Stack : Shape → Set where
  ∅ : Stack []
  _::_ : ∀ {u s} → el u → Stack s → Stack (Val u ∷ s)
  _!!_ : ∀ {u s} → Exp u → Stack s → Stack (Han u ∷ s)

-- Code concatenation.
infixr 6 _⊕_
_⊕_ : ∀ {s t u} → Code s t → Code t u → Code s u
_⊕_ cnil      cs = cs
_⊕_ (i ,, is) cs = i ,, (is ⊕ cs)
