module Machine where

open import Function
open import Data.List
open import Data.Sum
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import TypeUniverse
open import Expression

-- Stack items.
data Item : Set where
  Val : U → Item
  Han : U → Item

-- Shape of the stack.
Shape : Set
Shape = List Item

handlers : Shape → List U
handlers [] = []
handlers (Val u ∷ xs) = handlers xs
handlers (Han u ∷ xs) = u ∷ handlers xs

mutual
  data Instr : List U → Shape → List U → Shape → Set where
    PUSH   : ∀ {u s hs} → (x : el u) → Instr hs s hs (Val u ∷ s)
    ADD    : ∀ {s hs} → Instr hs (Val Nat ∷ Val Nat ∷ s) hs (Val Nat ∷ s)
    MARK   : ∀ {u s hs} → (h : Code (handlers s) s (Val u ∷ s)) → Instr hs s (u ∷ hs) (Han u ∷ s)
    UNMARK : ∀ {u s hs} → Instr (u ∷ hs) (Val u ∷ Han u ∷ s) hs (Val u ∷ s)
    THROW  : ∀ {u s hs} → Instr hs s hs (Val u ∷ s)

  data Code : List U → Shape → Shape → Set where
    ε : ∀ {s} → Code [] s s
    _◅_ : ∀ {hs s ht t r} → (i : Instr hs s ht t) → (is : Code ht t r) → Code hs s r

infixr 3 _::_
infixr 3 _!!_
data Stack : Shape → Set where
  snil : Stack []
  _::_ : ∀ {u s} → el u → Stack s → Stack (Val u ∷ s)
  _!!_ : ∀ {u s} → Code (handlers s) s (Val u ∷ s) → Stack s → Stack (Han u ∷ s)

data State (r : Shape) : Set where
  ✓[_,_,_] : ∀ {s hs} → Code hs s r → Stack s → hs ≡ handlers s → State r
  ×[] : State r

data Result (r : Shape) : Set where
  Success : Stack r → Result r
  Failure : Result r




