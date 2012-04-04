module Execution.Termination where

open import Function
open import Data.Nat
open import Data.Sum
open import Data.List
open import Data.Star
open import Data.Unit
open import Data.Maybe
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import TypeUniverse
open import Expression
open import Denotation
open import Code
open import Execution.Informative
open import Execution.Utils

data Balanced : ∀ {s t} → ℕ → Code s t → Set where
  bal-ε : ∀ {s} → Balanced {s} {s} zero ε
  bal-Push : ∀ {s t u n} {x : el u} {c : Code (Val u ∷ s) t} → Balanced n c → Balanced n (PUSH x ◅ c)
  bal-Add : ∀ {s t n} {c : Code (Val Nat ∷ s) t} → Balanced n c → Balanced n (ADD ◅ c)
  bal-Throw : ∀ {s t u n} {c : Code (Val u ∷ s) t} → Balanced n c → Balanced n (THROW ◅ c)
  bal-Mark : ∀ {s t u n} {c : Code (Han u ∷ s) t} {h : Code s (Val u ∷ s)}
    → Balanced zero h
    → Balanced (suc n) c
    → Balanced n (MARK h ◅ c)
  bal-Unmark : ∀ {s t u n} {c : Code (Val u ∷ s) t}
    → Balanced n c
    → Balanced (suc n) (UNMARK ◅ c)

Closed : ∀ {s t} → Code s t → Set
Closed {s} {t} c = Balanced zero c

BalancedCode : ℕ → Shape → Shape → Set
BalancedCode n s t = Σ[ c ∶ Code s t ] Balanced n c

ClosedCode : Shape → Shape → Set
ClosedCode s t = BalancedCode zero s t

data Fork : (s t : Shape) → Set where
  Push : ∀ {u s} → Fork s (Val u ∷ s)
  Add : ∀ {s} → Fork (Val Nat ∷ Val Nat ∷ s) (Val Nat ∷ s)
  Branch : ∀ {u s} → Star Fork (Han u ∷ s) (Val u ∷ Han u ∷ s) → Star Fork s (Val u ∷ s) → Fork s (Val u ∷ s)

Forks : Shape → Shape → Set
Forks = Star Fork

record Decomposition {s t : Shape} (n : ℕ) (c : Code s t) : Set where
  constructor Dec
  field
    u : U
    uw=u : unwindHnd s n ≡ just u
    main : BalancedCode n s (Val u ∷ Han u ∷ unwindShape s n)
    rest : ClosedCode (Val u ∷ unwindShape s n) t

decompose : ∀ {s t n} (c : Code s t) → Balanced (suc n) c → Decomposition n c
decompose {s} {t} {n} .(PUSH x ◅ c) (bal-Push {.s} {.t} {u} {.(suc n)} {x} {c} pf)
  with decompose c pf
... | Dec v p (m , mc) r = Dec v p (PUSH x ◅ m , bal-Push mc) r
decompose .{Val Nat ∷ Val Nat ∷ s} {t} {n} .(ADD ◅ c) (bal-Add {s} {.t} {.(suc n)} {c} pf)
  with decompose c pf
... | Dec v p (m , mc) r = Dec v p (ADD ◅ m , bal-Add mc) r
decompose {s} {t} {n} .(THROW ◅ c) (bal-Throw {.s} {.t} {u} {.(suc n)} {c} pf)
  with decompose c pf
... | Dec v p (m , mc) r = Dec v p (THROW ◅ m , bal-Throw mc) r
decompose {s} {t} {n} .(MARK h ◅ c) (bal-Mark {.s} {.t} {u} {.(suc n)} {c} {h} hc pf)
  with decompose c pf
... | Dec v p (m , mc) r = Dec v p (MARK h ◅ m , bal-Mark hc mc) r
decompose {.(Val u ∷ Han u ∷ s)} {t} {suc n} .(UNMARK ◅ c) (bal-Unmark {s} {.t} {u} {.(suc n)} {c} pf)
  with decompose c pf
... | Dec v p (m , mc) r = Dec v p ((UNMARK ◅ m) , (bal-Unmark mc)) r
decompose {.(Val u ∷ Han u ∷ s)} {t} {zero} .(UNMARK ◅ c) (bal-Unmark {s} {.t} {u} {.0} {c} pf)
  = Dec u refl (ε , bal-ε) (c , pf)

rehash : ∀ {s t} → (c : Code s t) → (pf : Closed c) → Forks s t
rehash ε pf = ε
rehash (PUSH x ◅ xs) (bal-Push  pf) = Push ◅ rehash xs pf
rehash (ADD    ◅ xs) (bal-Add   pf) = Add  ◅ rehash xs pf
rehash (THROW  ◅ xs) (bal-Throw pf) = Push ◅ rehash xs pf
rehash (MARK h ◅ xs) (bal-Mark hClosed pf) with decompose xs pf
... | Dec u refl (m , mClosed) (r , rClosed) = Branch (rehash m mClosed) (rehash h hClosed) ◅ rehash r rClosed
rehash (UNMARK ◅ xs) ()
