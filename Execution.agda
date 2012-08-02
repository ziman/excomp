module Execution where

open import Function
open import Data.Nat
open import Data.Star

open import Code

-- Execute a single instruction.
execInstr : ∀ {s t} → Instr s t → Stack s → Stack t
execInstr (PUSH x) st               =  x      :-: st
execInstr ADD      (x :-: y :-: st) = (x + y) :-: st

-- Execute a code block above the given stack.
execCode : ∀ {s t} → Code s t → Stack s → Stack t
execCode ε = id
execCode (i ◅ is) = execCode is ∘ execInstr i

