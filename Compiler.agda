module Compiler where

open import Function
open import Data.List
open import Data.Star

open import Expression
open import Code

-- Create a single-instruction code block.
⟦_⟧ : ∀ {s t} → Instr s t → Code s t
⟦ i ⟧ = i ◅ ε

-- Translate operators to instructions.
opInstr : ∀ {s t u} → Op s t u → ∀ {st} → Instr (s ∷ t ∷ st) (u ∷ st)
opInstr Plus = ADD

-- Compile expressions to the corresponding code.
compile : ∀ {u} → Exp u → ∀ {st} → Code st (u ∷ st)
compile (Lit n)      = ⟦ PUSH n ⟧
compile (Bin op l r) = compile r ◅◅ compile l ◅◅ ⟦ opInstr op ⟧
