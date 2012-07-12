module TypeUniverse where

open import Function
open import Data.Bool
open import Data.Nat
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- Types available in the modelled language.
data U : Set where
  nat : U
  bool : U
  _⇒_ : U → U → U

-- Interpretation of the types into Agda types.
el : U → Set
el nat     = ℕ
el bool    = Bool
el (x ⇒ y) = el x → el y

