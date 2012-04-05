module Execution.Termination where

open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.List
open import Data.Star
open import Data.Unit hiding (_≤_)
open import Data.Maybe
open import Data.Product

open import Algebra
open import Algebra.Structures
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import TypeUniverse
open import Expression
open import Denotation
open import Code
open import Execution.Informative
open import Execution.Utils
open import Execution.Forks

term' : ∀ {s t st} → (c : Code s t) → Closed c → Forks s t → AccCode s t c st
term' c pf f = {!!}

term : ∀ {s t st} → (c : Code s t) → Closed c → AccCode s t c st
term c pf = term' c pf (rehash c pf (size c) ≤-refl)

