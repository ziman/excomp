module Denotation where

open import Data.Nat

open import TypeUniverse
open import Expression

-- Denotation of operators.
denOp : ∀ {u v w} → Op u v w → el u → el v → el w
denOp Plus = _+_

-- Denotation of expressions.
denExp : ∀ {u} → Exp u → el u
denExp (Lit n)      = n
denExp (Bin op l r) = denOp op (denExp l) (denExp r)
