module Compiler where

open import Function
open import Data.Nat
open import Data.List

open import TypeUniverse
open import Expression
open import Denotation
open import Code

opInstr : ∀ {s t u v} → Op s t u → Instr (s ∷ t ∷ v) (u ∷ v)
opInstr Plus = ADD

compile : ∀ {u v} → Exp u → Code v (u ∷ v)
compile (Lit n)      = _,,_ (PUSH n)
compile (Bin op l r) = compile r ∘ compile l ∘ _,,_ (opInstr op)
