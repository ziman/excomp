module Execution.Forks where

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

data Forks : {s t : Shape} → Code s t → Set where
  Nil : ∀ {s} → Forks {s} {s} ε
  Push : ∀ {s t u} {x : el u} {is : Code (Val u ∷ s) t} → Forks is → Forks (PUSH x ◅ is)
  Throw : ∀ {s t u} {is : Code (Val u ∷ s) t} → Forks is → Forks (THROW ◅ is)
  Add : ∀ {s t} {is : Code (Val Nat ∷ s) t} → Forks is → Forks (ADD ◅ is)
  Branch : ∀ {u s t} {r : Code (Han u ∷ s) (Val u ∷ Han u ∷ s)}
    {h : Code s (Val u ∷ s)} {hc : Closed h} {is : Code (Val u ∷ s) t}
    → Forks r → Forks h → Forks is → Forks (MARK h hc ◅ r ◅◅ UNMARK ◅ is)

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
decompose {s} {t} {n} .(MARK h hc ◅ c) (bal-Mark {.s} {.t} {u} {.(suc n)} {c} {h} hc pf)
  with decompose c pf
... | Dec v p (m , mc) r = Dec v p (MARK h hc ◅ m , bal-Mark hc mc) r
decompose {.(Val u ∷ Han u ∷ s)} {t} {suc n} .(UNMARK ◅ c) (bal-Unmark {s} {.t} {u} {.(suc n)} {c} pf)
  with decompose c pf
... | Dec v p (m , mc) r = Dec v p ((UNMARK ◅ m) , (bal-Unmark mc)) r
decompose {.(Val u ∷ Han u ∷ s)} {t} {zero} .(UNMARK ◅ c) (bal-Unmark {s} {.t} {u} {.0} {c} pf)
  = Dec u refl (ε , bal-ε) (c , pf)

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans {m} {n} {o} p q = begin m ≤⟨ p ⟩ n ≤⟨ q ⟩ o ∎
  where
    open ≤-Reasoning

infixl 1 _≤≤_
_≤≤_ : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
_≤≤_ x y = ≤-trans x y 

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
size (MARK h _ ◅ is) = 1 + size h + size is
size (UNMARK ◅ is) = 1 + size is
size (THROW  ◅ is) = 1 + size is

dec-size₁ : ∀ {s t n} (c : Code s t) (pf : Balanced (suc n) c)
  → size (proj₁ (Decomposition.main (decompose c pf))) ≤ size c
dec-size₁ ε ()
dec-size₁ (PUSH x ◅ is) (bal-Push pf) = s≤s (dec-size₁ is pf)
dec-size₁ (ADD    ◅ is) (bal-Add  pf) = s≤s (dec-size₁ is pf)
dec-size₁ (THROW  ◅ is) (bal-Throw pf) = s≤s (dec-size₁ is pf)
dec-size₁ (MARK h hc ◅ is) (bal-Mark .hc pf) = s≤s (≤-plus (size h) (dec-size₁ is pf))
dec-size₁ {Val u ∷ Han .u ∷ s} {t} {suc n} (UNMARK ◅ is) (bal-Unmark pf) = s≤s (dec-size₁ is pf)
dec-size₁ {Val u ∷ Han .u ∷ s} {t} {zero } (UNMARK ◅ is) (bal-Unmark pf) = z≤n

dec-size₂ : ∀ {s t n} (c : Code s t) (pf : Balanced (suc n) c)
  → size (proj₁ (Decomposition.rest (decompose c pf))) ≤ size c
dec-size₂ ε ()
dec-size₂ (PUSH x ◅ is) (bal-Push pf) = ≤-step (dec-size₂ is pf)
dec-size₂ (ADD    ◅ is) (bal-Add  pf) = ≤-step (dec-size₂ is pf)
dec-size₂ (THROW  ◅ is) (bal-Throw pf) = ≤-step (dec-size₂ is pf)
dec-size₂ (MARK h hc ◅ is) (bal-Mark .hc pf) = ≤-step (≤-trans (dec-size₂ is pf) (n≤m+n (size h) (size is)))
dec-size₂ {Val u ∷ Han .u ∷ s} {t} {suc n} (UNMARK ◅ is) (bal-Unmark pf) = ≤-step (dec-size₂ is pf)
dec-size₂ {Val u ∷ Han .u ∷ s} {t} {zero } (UNMARK ◅ is) (bal-Unmark pf) = ≤-step ≤-refl

dec-comp : ∀  {s t n} (c : Code s t) (pf : Balanced (suc n) c)
  → let dec = decompose c pf in
        proj₁ (Decomposition.main dec) ◅◅ UNMARK ◅ proj₁ (Decomposition.rest dec) ≡ c
dec-comp ε ()
dec-comp (PUSH x ◅ is) (bal-Push    pf) rewrite dec-comp is pf = refl
dec-comp (ADD    ◅ is) (bal-Add     pf) rewrite dec-comp is pf = refl
dec-comp (MARK h hc ◅ is) (bal-Mark .hc pf) rewrite dec-comp is pf = refl
dec-comp (THROW  ◅ is) (bal-Throw   pf) rewrite dec-comp is pf = refl
dec-comp {Val u ∷ Han .u ∷ s} {t} {zero } (UNMARK ◅ is) (bal-Unmark pf) = refl
dec-comp {Val u ∷ Han .u ∷ s} {t} {suc n} (UNMARK ◅ is) (bal-Unmark pf) rewrite dec-comp is pf = refl

fork' : ∀ {s t} → (c : Code s t) → (pf : Closed c) → (m : ℕ) → (m ≥ size c) → Forks c
fork' ε _ _ _ = Nil
fork' (UNMARK ◅ xs) () _ _
fork' (PUSH _ ◅ _) _ zero ()
fork' (ADD    ◅ _) _ zero ()
fork' (THROW  ◅ _) _ zero ()
fork' (MARK _ _ ◅ _) _ zero ()
fork' (PUSH x ◅ xs) (bal-Push  pf) (suc m) (s≤s p) = Push  (fork' xs pf m p)
fork' (ADD    ◅ xs) (bal-Add   pf) (suc m) (s≤s p) = Add   (fork' xs pf m p)
fork' (THROW  ◅ xs) (bal-Throw pf) (suc m) (s≤s p) = Throw (fork' xs pf m p)
fork' (MARK h hClosed ◅ xs) (bal-Mark .hClosed pf) (suc n) (s≤s p)
  with decompose xs pf | dec-size₁ xs pf | dec-size₂ xs pf | dec-comp xs pf
fork' (MARK h hClosed ◅ .(m ◅◅ UNMARK ◅ r)) (bal-Mark .hClosed pf) (suc n) (s≤s p)
  | Dec u refl (m , mClosed) (r , rClosed) | pf₁ | pf₂ | refl
  = Branch
    (fork' m mClosed n (pf₁ ≤≤ n≤m+n (size h) (size xs') ≤≤ p))
    (fork' h hClosed n (m≤m+n (size h) (size xs') ≤≤ p))
    (fork' r rClosed n (pf₂ ≤≤ n≤m+n (size h) (size xs') ≤≤ p))
  where
    xs' = m ◅◅ UNMARK ◅ r

fork : ∀ {s t} (c : Code s t) → Closed c → Forks c
fork c pf = fork' c pf (size c) ≤-refl
