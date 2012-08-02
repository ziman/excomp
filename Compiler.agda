module Compiler where

open import Data.List
open import Data.Star

open import Expression
open import Code

-- Translate operators to instructions.
opInstr : ∀ {s t u v} → Op s t u → Instr (Val s ∷ Val t ∷ v) (Val u ∷ v)
opInstr Plus = ADD

-- Singleton code
⟦_⟧ : ∀ {s t} → Instr s t → Code s t
⟦_⟧ i = i ◅ ε

-- Compile expressions to the corresponding code.
compile : ∀ {u s} → Exp u → Code s (Val u ∷ s)
compile (Lit n)      = ⟦ PUSH n ⟧
compile Throw        = ⟦ THROW ⟧
compile (Catch e h)  = ⟦ MARK ⟧ ◅◅ compile e ◅◅ ⟦ HANDLE ⟧ ◅◅ compile h ◅◅ ⟦ UNMARK ⟧
compile (Bin op l r) = compile r ◅◅ compile l ◅◅ ⟦ opInstr op ⟧
