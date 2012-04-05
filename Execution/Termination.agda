module Execution.Termination where

open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.List
open import Data.Star
open import Data.Unit hiding (_≤_)
open import Data.Maybe
open import Data.Product

open import Algebra
open import Algebra.Structures
open import Relation.Binary
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

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans {m} {n} {o} p q = begin m ≤⟨ p ⟩ n ≤⟨ q ⟩ o ∎
  where
    open ≤-Reasoning

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero } = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-plus : ∀ {m n} o → m ≤ n → o + m ≤ o + n
≤-plus {m} {n} zero    p = p
≤-plus {m} {n} (suc o) p = s≤s (≤-plus o p)

size : ∀ {s t} → Code s t → ℕ
size ε        = zero
size (PUSH _ ◅ is) = 1 + size is
size (ADD    ◅ is) = 1 + size is
size (MARK h ◅ is) = 1 + size h + size is
size (UNMARK ◅ is) = 1 + size is
size (THROW  ◅ is) = 1 + size is

dec-size₁ : ∀ {s t n} (c : Code s t) (pf : Balanced (suc n) c)
  → suc (size (proj₁ (Decomposition.main (decompose c pf)))) ≤ size c
dec-size₁ ε ()
dec-size₁ (PUSH x ◅ is) (bal-Push pf) = s≤s (dec-size₁ is pf)
dec-size₁ (ADD    ◅ is) (bal-Add  pf) = s≤s (dec-size₁ is pf)
dec-size₁ (THROW  ◅ is) (bal-Throw pf) = s≤s (dec-size₁ is pf)
dec-size₁ (MARK h ◅ is) (bal-Mark hc pf) = s≤s {!!} -- s≤s (≤-plus (size h) (dec-size₁ is pf))
dec-size₁ {Val u ∷ Han .u ∷ s} {t} {suc n} (UNMARK ◅ is) (bal-Unmark pf) = s≤s (dec-size₁ is pf)
dec-size₁ {Val u ∷ Han .u ∷ s} {t} {zero } (UNMARK ◅ is) (bal-Unmark pf) = s≤s z≤n

dec-size₂ : ∀ {s t n} (c : Code s t) (pf : Balanced (suc n) c)
  → suc (size (proj₁ (Decomposition.rest (decompose c pf)))) ≤ size c
dec-size₂ ε ()
dec-size₂ (PUSH x ◅ is) (bal-Push pf) = ≤-step (dec-size₂ is pf)
dec-size₂ (ADD    ◅ is) (bal-Add  pf) = ≤-step (dec-size₂ is pf)
dec-size₂ (THROW  ◅ is) (bal-Throw pf) = ≤-step (dec-size₂ is pf)
dec-size₂ (MARK h ◅ is) (bal-Mark hc pf) = ≤-step (≤-trans (dec-size₂ is pf) (n≤m+n (size h) (size is)))
dec-size₂ {Val u ∷ Han .u ∷ s} {t} {suc n} (UNMARK ◅ is) (bal-Unmark pf) = ≤-step (dec-size₂ is pf)
dec-size₂ {Val u ∷ Han .u ∷ s} {t} {zero } (UNMARK ◅ is) (bal-Unmark pf) = ≤-refl

rehash : ∀ {s t} → (c : Code s t) → (pf : Closed c) → (m : ℕ) → (m ≥ size c) → Forks s t
rehash ε _ _ _ = ε
rehash (UNMARK ◅ xs) () _ _
rehash (PUSH _ ◅ _) _ zero ()
rehash (ADD    ◅ _) _ zero ()
rehash (THROW  ◅ _) _ zero ()
rehash (MARK _ ◅ _) _ zero ()
rehash (PUSH x ◅ xs) (bal-Push  pf) (suc m) (s≤s p) = Push ◅ rehash xs pf m p
rehash (ADD    ◅ xs) (bal-Add   pf) (suc m) (s≤s p) = Add  ◅ rehash xs pf m p
rehash (THROW  ◅ xs) (bal-Throw pf) (suc m) (s≤s p) = Push ◅ rehash xs pf m p
rehash (MARK h ◅ xs) (bal-Mark hClosed pf) (suc n) (s≤s p) with decompose xs pf
... | Dec u refl (m , mClosed) (r , rClosed) =
  Branch
    (rehash m mClosed n {!≤-trans (dec-size₁ xs pf) (n≤m+n (size h) (size xs))!})
    (rehash h hClosed n (≤-trans (m≤m+n (size h) (size xs)) p))
  ◅ rehash r rClosed n {!≤-trans (dec-size₂ xs pf) (n≤m+n (size h) (size xs))!}
