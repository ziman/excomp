module Code where

open import Function
open import Data.List
open import Data.Sum
open import Data.Maybe

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
  data i[_,_]→[_,_] : Shape → List Shape → Shape → List Shape → Set where
    PUSH : ∀ {u s w}
      → el u
      → i[ s , w ]→[ Val u ∷ s , w ]
    ADD : ∀ {s w}
      → i[ Val Nat ∷ Val Nat ∷ s , w ]→[ Val Nat ∷ s , w ]
    MARK : ∀ {u s w}
      → c[ s , w ]→[ Val u ∷ s , w ]
      → i[ s , w ]→[ Han u ∷ s , s ∷ w ]
    UNMARK : ∀ {u s v w}
      → i[ Val u ∷ Han u ∷ s , v ∷ w ]→[ Val u ∷ s , w ]
    THROW : ∀ {u s w}
      → i[ s , w ]→[ Val u ∷ s , w ]

  -- Code is an (indexed) list of instructions.
  infixr 50 _,,_
  data c[_,_]→[_,_] : Shape → List Shape → Shape → List Shape → Set where
    cnil : ∀ {s w}
      → c[ s , w ]→[ s , w ]
    _,,_ : ∀ {s₁ w₁ s₂ w₂ s₃ w₃}
      → i[ s₁ , w₁ ]→[ s₂ , w₂ ]
      → c[ s₂ , w₂ ]→[ s₃ , w₃ ]
      → c[ s₁ , w₁ ]→[ s₃ , w₃ ]

-- Stack w s is the type of stacks where:
-- * `s' is the current shape of the stack
-- * `w' is the stack (cons-list) of "throw resume-points",
--   where a "resume-point" is a stack shape where execution
--   would reinstate if we threw an exception right now.
infixr 50 _::_
infixr 50 _!!_
data Stack : Shape → List Shape → Set where
  snil : Stack [] []
  _::_ : ∀ {u w s}
    → el u
    → Stack s w
    → Stack (Val u ∷ s) w
  _!!_ : ∀ {u w s}
    → c[ s , w ]→[ Val u ∷ s , w ]
    → Stack s w
    → Stack (Han u ∷ s) (s ∷ w)

-- Code concatenation.
infixr 60 _⊕_
_⊕_ : ∀ {s₁ w₁ s₂ w₂ s₃ w₃}
  → c[ s₁ , w₁ ]→[ s₂ , w₂ ]
  → c[ s₂ , w₂ ]→[ s₃ , w₃ ]
  → c[ s₁ , w₁ ]→[ s₃ , w₃ ]
_⊕_ cnil      cs = cs
_⊕_ (i ,, is) cs = i ,, (is ⊕ cs)

-- Promote an instruction to code.
⟦_⟧ : ∀ {s₁ w₁ s₂ w₂}
  → i[ s₁ , w₁ ]→[ s₂ , w₂ ]
  → c[ s₁ , w₁ ]→[ s₂ , w₂ ]
⟦_⟧ i = i ,, cnil
