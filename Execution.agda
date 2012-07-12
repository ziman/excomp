module Execution where

open import Function using (_∘_; id)
open import Data.Nat
open import Data.Star

open import TypeUniverse
open import Expression
open import Denotation
open import Code
open import Compiler

-- Execute a single instruction.
execInstr : ∀ {s t} → Instr s t → Stack s → Stack t
execInstr (PUSH x) st               =  x  :-: st
execInstr APPLY    (f :-: x :-: st) = f x :-: st

-- Execute a code block above the given stack.
execCode : ∀ {s t} → Code s t → Stack s → Stack t
execCode ε = id
execCode (i ◅ is) = execCode is ∘ execInstr i

