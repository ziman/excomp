module Compiler where

open import Function
open import Data.Nat
open import Data.List

open import TypeUniverse
open import Expression
open import Denotation
open import Code

single : ∀ {s t} → Instr s t → Code s t
single i = i ,, cnil

opInstr : ∀ {s t u v} → Op s t u → Instr (s ∷ t ∷ v) (u ∷ v)
opInstr Plus = ADD

compile : ∀ {u v} → Exp u → Code v (u ∷ v)
compile (Lit n)      = single (PUSH n)
compile (Bin op l r) = compile r ⊕ compile l ⊕ single (opInstr op)
