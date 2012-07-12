module Denotation where

open import Data.Nat

open import TypeUniverse
open import Expression

-- Denotation of expressions.
denExp : ∀ {u} → Exp u → el u
denExp (Lit n) = n
denExp (f $ x) = (denExp f) (denExp x)

private
  -- Usage: C-c C-n example
  example : ℕ
  example = denExp (Lit _+_ $ Lit 3 $ Lit 4)
