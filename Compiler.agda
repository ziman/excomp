module Compiler where

open import Function
open import Data.Nat
open import Data.List

open import TypeUniverse
open import Expression
open import Denotation
open import Code

-- Create a single-instruction code block.
single : ∀ {s t} → Instr s t → Code s t
single i = i ,, cnil

-- Translate operators to instructions.
opInstr : ∀ {s t u v} → Op s t u → Instr (s ∷ t ∷ v) (u ∷ v)
opInstr Plus = ADD

-- Compile expressions to the corresponding code.
compile : ∀ {u v} → Exp u → Code v (u ∷ v)
compile (Lit n)      = single (PUSH n)
compile (Bin op l r) = compile r ⊕ compile l ⊕ single (opInstr op)
