module TypeUniverse where

open import Data.Nat
open import Data.Bool

-- Types available in the modelled language.
data U : Set where
  nat : U
  bool : U

-- Interpretation of the types into Agda types.
el : U → Set
el nat  = ℕ
el bool = Bool
