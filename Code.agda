module Code where

open import Function
open import Data.List
open import Data.Sum
open import Data.Maybe
open import Data.Star
open import Data.Nat
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

mutual
  -- Instructions of the stack machine.
  data Instr : Shape → Shape → Set where
    PUSH : ∀ {u s} → el u → Instr s (Val u ∷ s)
    ADD : ∀ {s} → Instr (Val Nat ∷ Val Nat ∷ s) (Val Nat ∷ s)
    MARK : ∀ {u s} → (c : Code s (Val u ∷ s)) → Balanced zero c → Instr s (Han u ∷ s)
    UNMARK : ∀ {u s} → Instr (Val u ∷ Han u ∷ s) (Val u ∷ s)
    THROW : ∀ {u s} → Instr s (Val u ∷ s)

  -- Code is an (indexed) list of instructions.
  Code : Shape → Shape → Set
  Code = Star Instr

  data Balanced : ∀ {s t} → ℕ → Code s t → Set where
    bal-ε : ∀ {s} → Balanced {s} {s} zero ε
    bal-Push : ∀ {s t u n} {x : el u} {c : Code (Val u ∷ s) t} → Balanced n c → Balanced n (PUSH x ◅ c)
    bal-Add : ∀ {s t n} {c : Code (Val Nat ∷ s) t} → Balanced n c → Balanced n (ADD ◅ c)
    bal-Throw : ∀ {s t u n} {c : Code (Val u ∷ s) t} → Balanced n c → Balanced n (THROW ◅ c)
    bal-Mark : ∀ {s t u n} {c : Code (Han u ∷ s) t} {h : Code s (Val u ∷ s)}
      → (hb : Balanced zero h)
      → Balanced (suc n) c
      → Balanced n (MARK h hb ◅ c)
    bal-Unmark : ∀ {s t u n} {c : Code (Val u ∷ s) t}
      → Balanced n c
      → Balanced (suc n) (UNMARK ◅ c)

irrBalanced : ∀ {s t n} (c : Code s t) (p q : Balanced n c) → p ≡ q
irrBalanced ε bal-ε bal-ε = refl
irrBalanced (PUSH x ◅ is) (bal-Push p) (bal-Push q) = cong _ (irrBalanced is p q)
irrBalanced (ADD ◅ is) (bal-Add p) (bal-Add q) = cong _ (irrBalanced is p q)
irrBalanced (THROW ◅ is) (bal-Throw p) (bal-Throw q) = cong _ (irrBalanced is p q)
irrBalanced (MARK h hc ◅ is) (bal-Mark .hc p) (bal-Mark .hc q) = cong _ (irrBalanced is p q)
irrBalanced (UNMARK ◅ is) (bal-Unmark p) (bal-Unmark q) = cong _ (irrBalanced is p q)

Closed : ∀ {s t} → Code s t → Set
Closed {s} {t} c = Balanced zero c

BalancedCode : ℕ → Shape → Shape → Set
BalancedCode n s t = Σ[ c ∶ Code s t ] Balanced n c

ClosedCode : Shape → Shape → Set
ClosedCode s t = BalancedCode zero s t

unwindHnd : Shape → ℕ → Maybe U
unwindHnd (Han u ∷ xs) zero    = just u
unwindHnd (Han _ ∷ xs) (suc n) = unwindHnd xs n
unwindHnd (Val _ ∷ xs) n       = unwindHnd xs n
unwindHnd []           _       = nothing

unwindShape : Shape → ℕ → Shape
unwindShape (Han _ ∷ xs) zero    = xs
unwindShape (Han _ ∷ xs) (suc n) = unwindShape xs n
unwindShape (Val _ ∷ xs) n       = unwindShape xs n
unwindShape []           _       = []

