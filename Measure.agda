module Measure where

open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Induction.Nat renaming (<-well-founded to <′-well-founded)
open import Induction.WellFounded

open import Machine

measureCode : ∀ {hs s t} → Code hs s t → ℕ
measureCode ε = zero
measureCode (PUSH x ◅ is) = suc (measureCode is)
measureCode (ADD    ◅ is) = suc (measureCode is)
measureCode (MARK h ◅ is) = suc (measureCode is + measureCode h)
measureCode (UNMARK ◅ is) = suc (measureCode is)
measureCode (THROW  ◅ is) = suc (measureCode is)

measureStack : ∀ {s} → Stack s → ℕ
measureStack snil = zero
measureStack (x :: xs) = suc (measureStack xs)
measureStack (h !! xs) = suc (measureCode h + measureStack xs)

measureState : ∀ {r} → State r → ℕ
measureState ×[] = zero
measureState ✓[ code , stack , eq ] = measureCode code + measureStack stack

module MeasureWF (a : Set) (measure : a → ℕ) where
  module <-<′-equivalence where
    unacc : ∀ {a : Set} {P} {x : a} → Acc P x → (∀ y → P y x → Acc P y)
    unacc (acc stuff) = stuff

    acc'⇒acc : ∀ x → Acc _<′_ x → Acc _<_ x 
    acc'⇒acc x (acc acc-x) = acc λ y y<x → acc'⇒acc y (acc-x y (≤⇒≤′ y<x))

    wf'⇒wf : Well-founded _<′_ → Well-founded _<_
    wf'⇒wf <'-wf x = acc (λ y y<x → acc'⇒acc y (unacc (<'-wf x) y (≤⇒≤′ y<x)))
  
  wf : Well-founded (_<_ on measure)
  wf = inv-wf (wf'⇒wf <′-well-founded)
    where
      open <-<′-equivalence
      open Inverse-image {A = a} {_<_ = _<_} measure renaming (well-founded to inv-wf)

_<'_ : ∀ {r} → State r → State r → Set
_<'_ = _<_ on measureState

<'-well-founded : ∀ {r} → Well-founded (_<'_ {r})
<'-well-founded {r} = wf where open MeasureWF (State r) measureState
