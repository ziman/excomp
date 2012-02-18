module Compiler where

open import Function
open import Data.Nat
open import Data.List

open import TypeUniverse
open import Expression
open import Denotation
open import Code

-- [CGen s t r] represents code transforming a stack of shape [s]
-- into a stack of shape [t], leaving the total result type open.
CGen : Shape → Shape → Set
CGen s t = {r : Shape} → Code t r → Code s r

compileOp : ∀ {s t u v} → Op s t u → CGen (s ∷ t ∷ v) (u ∷ v)
compileOp Plus = _,,_ ADD

compile : ∀ {u v} → Exp u → CGen v (u ∷ v)
compile (Lit n)      = _,,_ (PUSH n)
compile (Bin op l r) = compile r ∘ compile l ∘ compileOp op
