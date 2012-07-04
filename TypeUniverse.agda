module TypeUniverse where

open import Function
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- Types available in the modelled language.
data U : Set where
  nat : U
  bool : U

-- Interpretation of the types into Agda types.
el : U → Set
el nat  = ℕ
el bool = Bool

-- Equality of the types is decidable.
eqDecU : ∀ (x y : U) → Dec (x ≡ y)
eqDecU nat  nat  = yes refl
eqDecU bool bool = yes refl
eqDecU nat  bool = no λ ()
eqDecU bool nat  = no λ ()
