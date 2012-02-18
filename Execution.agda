module Execution where

open import Function
open import Data.Nat

open import TypeUniverse
open import Expression
open import Denotation
open import Code
open import Compiler

exec-instr : ∀ {s t} → Instr s t → Stack s → Stack t
exec-instr (PUSH x) st             =  x      :: st
exec-instr ADD      (x :: y :: st) = (x + y) :: st

exec-seq : ∀ {s t} → InstrSeq s t → Stack s → Stack t
exec-seq (i ,, is) = exec-seq is ∘ exec-instr i
exec-seq inil      = id

exec : ∀ {s t} → Code s t → Stack s → Stack t
exec code = exec-seq (code inil)
