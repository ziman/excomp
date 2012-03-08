module Compiler where

open import Function
open import Data.Nat
open import Data.List

open import TypeUniverse
open import Expression
open import Denotation
open import Code

-- Translate operators to instructions.
opInstr : ∀ {s t u v w} → Op s t u → i[ Val s ∷ Val t ∷ v , w ]→[ Val u ∷ v , w ]
opInstr Plus = ADD

-- Compile expressions to the corresponding code.
compile : ∀ {u s w} → (e : Exp u) → c[ s , w ]→[ Val u ∷ s , w ]
compile (Lit n)      = ⟦ PUSH n ⟧
compile Throw        = ⟦ THROW ⟧
compile (Catch e h)  = ⟦ MARK (compile h) ⟧ ⊕ compile e ⊕ ⟦ UNMARK ⟧
compile (Bin op l r) = compile r ⊕ compile l ⊕ ⟦ opInstr op ⟧
