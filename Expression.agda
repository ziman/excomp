module Expression where

open import TypeUniverse

data Op : U → U → U → Set where
  Plus : Op Nat Nat Nat

data Exp : U → Set where
  Lit : ∀ {u} → el u → Exp u
  Bin : ∀ {u v w} → Op u v w → Exp u → Exp v → Exp w
