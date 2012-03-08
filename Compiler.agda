module Compiler where

open import Function
open import Data.Nat
open import Data.List

open import TypeUniverse
open import Expression
open import Denotation
open import Code

-- Create a single-instruction code block.
⟦_⟧ : ∀ {s t} → Instr s t → Code s t
⟦_⟧ i = i ,, cnil

-- Translate operators to instructions.
opInstr : ∀ {s t u v} → Op s t u → Instr (Val s ∷ Val t ∷ v) (Val u ∷ v)
opInstr Plus = ADD

-- Compile expressions to the corresponding code.
compile : ∀ {u s} → (e : Exp u) → Code s (Val u ∷ s)
compile (Lit n)      = ⟦ PUSH n ⟧
compile Throw        = ⟦ THROW ⟧
compile (Catch e h)  = ⟦ MARK (compile h) ⟧ ⊕ compile e ⊕ ⟦ UNMARK ⟧
compile (Bin op l r) = compile r ⊕ compile l ⊕ ⟦ opInstr op ⟧
