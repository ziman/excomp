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

unfork : ∀ {s t} {c : Code s t} → Forks c → Code s t
unfork Nil            = ε
unfork (Throw      f) = THROW ◅ unfork f
unfork (Add        f) = ADD   ◅ unfork f
unfork (Branch r h f) = MARK (unfork h) ◅ unfork r ◅◅ UNMARK ◅ unfork f
unfork {c = PUSH x ◅ _} (Push  f) = PUSH x ◅ unfork f

cong₃ : ∀ {a b c d : Set} (P : a → b → c → d) {x x' : a} {y y' : b} {z z' : c}
  → x ≡ x' → y ≡ y' → z ≡ z'
  → P x y z ≡ P x' y' z'
cong₃ _ refl refl refl = refl

unfork-inv : ∀ {s t} (c : Code s t) → (pf : Closed c) → c ≡ unfork (fork c pf)
unfork-inv ε pf = refl
unfork-inv (UNMARK ◅ is) ()
unfork-inv (PUSH x ◅ is) (bal-Push  r) = cong (λ y → PUSH x ◅ y) (unfork-inv is r)
unfork-inv (THROW  ◅ is) (bal-Throw r) = cong (λ y → THROW  ◅ y) (unfork-inv is r)
unfork-inv (ADD    ◅ is) (bal-Add   r) = cong (λ y → ADD    ◅ y) (unfork-inv is r)
unfork-inv (MARK h ◅ is) (bal-Mark hr r) with decompose is r | dec-size₁ is r | dec-size₂ is r | dec-comp is r
unfork-inv (MARK h ◅ .(proj₁ main ◅◅ UNMARK ◅ proj₁ rest)) (bal-Mark hr r) | Dec u' refl main rest | pf₁ | pf₂ | refl
  = cong₃ (λ x y z → MARK x ◅ y ◅◅ UNMARK ◅ z) {!unfork-inv !} {!!} {!!}

{-
Acc : ∀ {s t} → Code s t → Set
Acc c = ∀ st → AccCode _ _ c st

acc-cons : ∀ {s t u} (i : Instr s t) (is : Code t u)
  → AccCode (i ◅ is) → AccCode is
acc-cons (PUSH x) is acc st with acc (execInstr (PUSH x) st aiPush)
... | z = ?
acc-cons (PUSH x) is acc ![ n , r ] = {!!}
acc-cons  ADD     is acc st = {!!}
acc-cons (MARK h) is acc st = {!!}
acc-cons  UNMARK  is acc st = {!!}
acc-cons  THROW   is acc st = {!!}
-}
{-
acc-app : ∀ {s t v u st} (c : Code s (Val v ∷ Han v ∷ t)) (d : Code (Val v ∷ t) u)
  → AccCode _ _ c st → (∀ st' → AccCode _ _ d st') → AccCode _ _ (c ◅◅ UNMARK ◅ d) st
acc-app {.(Val v ∷ Han v ∷ t)} {t} {v} {u} { ✓[ x :: h !! st ] } ε d ac ad = step aiUnmark✓ (ad ✓[ x :: st ])
acc-app {.(Val v ∷ Han v ∷ t)} {t} {v} {u} { ![ suc n , r ] } ε d ac ad = step aiUnmark! (ad ![ n , r ])
acc-app {Val v ∷ Han .v ∷ t} .{t} .{v} {u} { ![ zero , Okay .{v} h st ] } ε d ac ad = step (aiHandle {!!}) (ad _)
acc-app (PUSH x ◅ is) d (step aiPush  y) ad = step aiPush (acc-app is d y ad)
acc-app (ADD    ◅ is) d (step aiAdd   y) ad = step aiAdd (acc-app is d y ad)
acc-app (MARK h ◅ is) d (step aiMark  y) ad = step aiMark (acc-app is d y ad)
acc-app (THROW  ◅ is) d (step aiThrow y) ad = step aiThrow (acc-app is d y ad)
acc-app (UNMARK ◅ is) d (step aiUnmark✓ y) ad = step aiUnmark✓ (acc-app is d y ad)
acc-app (UNMARK ◅ is) d (step aiUnmark! y) ad = step aiUnmark! (acc-app is d y ad)
acc-app (UNMARK ◅ is) d (step (aiHandle hc) y) ad = step (aiHandle hc) (acc-app is d y ad)

term' : ∀ {s t} {c : Code s t} → Forks c → ∀ st → AccCode s t c st
term' Nil _ = trivial
term' (Push  f) st = step aiPush  (term' f _)
term' (Throw f) st = step aiThrow (term' f _)
term' (Add   f) st = step aiAdd   (term' f _)
term' (Branch {u} {s} {t} {r} {h} {is} rf hf isf) st
  = step aiMark (acc-app r is (term' rf _) (term' isf))
-}
{-
term : ∀ {s t st} → (c : Code s t) → Closed c → AccCode s t c st
term c pf = term' (rehash c pf (size c) ≤-refl)
-}
{-
-- health economics

It's this fascinating symbiosis of mind and machine where my most perverse ideas
get materialized in heavily dependent code.

-}
