module Expression where

open import TypeUniverse

-- The type of expressions of the modelled language.
infixl 50 _$_
data Exp : U → Set where
  Lit : ∀ {u} → el u → Exp u
  _$_ : ∀ {u v} → Exp (u ⇒ v) → Exp u → Exp v
