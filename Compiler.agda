module Compiler where

open import Data.Nat
open import Data.List
open import Data.Star

open import TypeUniverse
open import Expression
open import Denotation
open import Code

-- Create a single-instruction code block.
⟦_⟧ : ∀ {s t} → Instr s t → Code s t
⟦ i ⟧ = i ◅ ε

-- Compile expressions to the corresponding code.
compile : ∀ {u} → Exp u → ∀ {st} → Code st (u ∷ st)
compile (Lit n) = ⟦ PUSH n ⟧
compile (f $ x) = compile x ◅◅ compile f ◅◅ ⟦ APPLY ⟧
