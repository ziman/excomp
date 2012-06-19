module Execution where

open import Function
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.List
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming ([_] to insp)
open import Induction.WellFounded as WF

open import TypeUniverse
open import Expression
open import Denotation
open import Machine
open import Measure

∷-inj₂ : ∀ {a : Set} {x y : a} {xs ys : List a} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
∷-inj₂ refl = refl

step : ∀ {s hs t ht r}
  → (i : Instr hs s ht t)
  → (is : Code ht t r)
  → (st : Stack s)
  → (eq : hs ≡ handlers s)
  → State r
step (PUSH x) is            st  eq = ✓[ is ,     x :: st , eq ]
step  ADD     is (x :: y :: st) eq = ✓[ is , x + y :: st , eq ]
step (MARK h) is            st  eq = ✓[ is ,     h !! st , cong (λ us → _ ∷ us) eq ]
step  UNMARK  is (x :: h !! st) eq = ✓[ is ,     x :: st , ∷-inj₂ eq ]
step {s} THROW is st eq with handlers s
step THROW is st eq | [] = ×[]
step THROW is st eq | u ∷ us rewrite eq = {!!}


step-decr : ∀ {s hs t ht r}
  → (i : Instr hs s ht t)
  → (is : Code ht t r)
  → (st : Stack s)
  → (eq : hs ≡ handlers s)
  → measureState (step i is st eq) < measureState ✓[ i ◅ is , st , eq ]
step-decr i is st eq = {!!}

run' : ∀ {r} → (st : State r) → Acc _<'_ st → Result r
run' ×[] _ = Failure
run' ✓[ ε , st , eq ] (acc acc-st) = Success st
run' ✓[ i ◅ is , st , eq ] (acc acc-st) = run' next (acc-st next next-<)
  where
    next   = step i is st eq
    next-< = step-decr i is st eq

