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

acc-app : ∀ s t u (c : Code s t) (d : Code t u)
  → (∀ st → AccCode s t c st)
  → (∀ st → AccCode t u d st)
  → ∀ st → AccCode s u (c ◅◅ d) st
acc-app s t u c d ac ad st with ac st
acc-app s .s u .ε d ac ad st | trivial = ad st
acc-app .(Val Nat ∷ Val Nat ∷ s) t u .(ADD ◅ is) d ac ad st
  | step {.(Val Nat ∷ Val Nat ∷ s)} {.(Val Nat ∷ s)} {.t} {.ADD} {is} (aiAdd {s}) y
  with acc-app (Val Nat ∷ s) t u is d y ad
... | qqq = {!!}
acc-app s t u' .(PUSH x ◅ is) d ac ad st
  | step {.s} {.(Val u ∷ s)} {.t} {.(PUSH x)} {is} (aiPush {.s} {u} {x}) y
  = {!!}
acc-app s t u' .(THROW ◅ is) d ac ad st
  | step {.s} {.(Val u ∷ s)} {.t} {.THROW} {is} (aiThrow {._} {u}) y
  = {!!}
acc-app s t u' .(MARK h ◅ is) d ac ad st
  | step {.s} {.(Han u ∷ s)} {.t} {.(MARK h)} {is} (aiMark {.s} {u} {.st} {h}) y
  = {!!}
acc-app .(Val u ∷ Han u ∷ s) t u' .(UNMARK ◅ is) d ac ad .(✓[ st ])
  | step {.(Val u ∷ Han u ∷ s)} {.(Val u ∷ s)} {.t} {.UNMARK} {is} (aiUnmark✓ {s} {u} {st}) y
  = {!!}
acc-app .(Val u ∷ Han u ∷ s) t u' .(UNMARK ◅ is) d ac ad .(![ suc n , r ])
  | step {.(Val u ∷ Han u ∷ s)} {.(Val u ∷ s)} {.t} {.UNMARK} {is} (aiUnmark! {s} {u} {n} {r}) y
  = {!!}
acc-app .(Val u ∷ Han u ∷ s) t u' .(UNMARK ◅ is) d ac ad .(![ 0 , Okay h st ])
  | step {.(Val u ∷ Han u ∷ s)} {.(Val u ∷ s)} {.t} {.UNMARK} {is} (aiHandle {s} {u} {h} {st} y) y'
  = {!!}

term' : ∀ {s t} {c : Code s t} → Forks c → ∀ {st} → AccCode s t c st
term' Nil = trivial
term' (Push  f) = step aiPush (term' f)
term' (Throw f) = step aiThrow (term' f)
term' (Add   f) = step aiAdd (term' f)
term' (Branch r h f) = {!!}

term : ∀ {s t st} → (c : Code s t) → Closed c → AccCode s t c st
term c pf = term' (rehash c pf (size c) ≤-refl)

