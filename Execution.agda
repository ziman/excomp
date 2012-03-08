module Execution where

open import Function
open import Data.Nat
open import Data.Sum
open import Data.List

open import TypeUniverse
open import Expression
open import Denotation
open import Code

unwindHead : List Shape → Shape
unwindHead []      = []
unwindHead (s ∷ _) = s

unwindTail : List Shape → List Shape
unwindTail []       = []
unwindTail (_ ∷ ss) = ss

unwindStack : ∀ {s w} → Stack s w → Stack (unwindHead w) (unwindTail w)
unwindStack {_} {[]}     st = snil
unwindStack {_} {x ∷ xs} st = unwindStack' st
  where
    unwindStack' : ∀ {s x xs} → Stack s (x ∷ xs) → Stack x xs
    unwindStack' (_ :: xs) = unwindStack' xs
    unwindStack' (x !! xs) = xs

exec : ∀ {s₁ w₁ s₂ w₂}
  → c[ s₁ , w₁ ]→[ s₂ , w₂ ]
  → Stack s₁ w₁
  → Stack s₂ w₂ ⊎ Stack (unwindHead w₂) (unwindTail w₂)
exec cnil           st             = inj₁ st
exec (PUSH n ,, is) st             = exec is (n :: st)
exec (ADD    ,, is) (x :: y :: st) = exec is ((x + y) :: st)
exec (UNMARK ,, is) (x :: _ !! st) = exec is (x :: st)
exec (MARK h ,, is) st             = exec is (h !! st)
exec (THROW  ,, is) st             = exec {!!} {!!}

sample : Stack (Val Nat ∷ []) [] ⊎ Stack [] []
sample = exec (PUSH 3 ,, THROW ,, ADD ,, cnil) snil

