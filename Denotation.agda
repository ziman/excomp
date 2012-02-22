module Denotation where

open import Data.Nat
open import Data.Maybe

open import TypeUniverse
open import Expression

-- Denotation of operators.
denOp : ∀ {u v w} → Op u v w → el u → el v → el w
denOp Plus = _+_

-- Denotation of expressions.
denExp : ∀ {u} → Exp u → Maybe (el u)
denExp Throw        = nothing
denExp (Catch e h) with denExp e
... | just x  = just x
... | nothing = denExp h
denExp (Lit n)      = just n
denExp (Bin op l r) with denExp l | denExp r
... | just x | just y = just (denOp op x y)
... | _      | _      = nothing

private
  -- Usage: C-c C-n example₁
  example₁ : Maybe ℕ
  example₁ = denExp (Bin Plus (Lit 3) (Lit 4))
