module Expression where

open import TypeUniverse

-- The type of (binary) operators.
data Op : U → U → U → Set where
  Plus : Op Nat Nat Nat

-- The type of expressions of the modelled language.
data Exp : U → Set where
  Lit : ∀ {u} → el u → Exp u
  Bin : ∀ {u v w} → Op u v w → Exp u → Exp v → Exp w
