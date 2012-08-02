module TypeUniverse where

open import Function
open import Data.Nat
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- Types available in the modelled language.
data U : Set where
  Nat : U

-- Interpretation of the types into Agda types.
el : U → Set
el Nat      = ℕ
