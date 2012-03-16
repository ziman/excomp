module Execution where

open import Function
open import Data.Nat
open import Data.Sum
open import Data.List
open import Data.Star

open import TypeUniverse
open import Expression
open import Denotation
open import Code

data State : Shape → Set where
  ✓[_] : ∀ {s} → Stack s → State s
  ![_,_] : ∀ {s t} → ℕ → Stack t → State s

mutual
  execInstr : ∀ {s t} → Instr s t → State s → State t
  execInstr UNMARK   ![ zero , st ] = {!!}
  execInstr UNMARK   ![ suc n , st ] = ![ n , st ]
  execInstr (MARK _) ![ n , st ] = ![ suc n , st ]
  execInstr _        ![ n , st ] = ![ n , st ]
  execInstr (PUSH y) ✓[ st ] = ✓[ y :: st ]
  execInstr ADD      ✓[ x :: y :: st ] = ✓[ (x + y) :: st ]
  execInstr (MARK y) s' = {!!}
  execInstr UNMARK   s' = {!!}
  execInstr THROW    s' = {!!}

  exec : ∀ {s t} → Code s t → State s → State t
  exec ε        st = st
  exec (i ◅ is) st = exec is (execInstr i st)


