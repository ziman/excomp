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

postulate
  funext-dep : ∀ {a : Set} {b : a → Set} → (f g : (x : a) → b x) → (∀ x → f x ≡ g x) → f ≡ g

mutual
  irrInstr : ∀ {s t st} (i : Instr s t) (p q : AccInstr s t i st) → p ≡ q
  irrInstr ADD aiAdd aiAdd = refl
  irrInstr (PUSH x) aiPush aiPush = refl
  irrInstr THROW aiThrow aiThrow = refl
  irrInstr (MARK h) aiMark aiMark = refl
  irrInstr {Val u ∷ Han .u ∷ s} .{Val u ∷ s} { ✓[ st ] } UNMARK aiUnmark✓ aiUnmark✓ = refl
  irrInstr {Val u ∷ Han .u ∷ s} .{Val u ∷ s} { ![ suc n , r ] } UNMARK aiUnmark! aiUnmark! = refl
  irrInstr {Val u ∷ Han .u ∷ s} .{Val u ∷ s} { ![ zero , Okay h st ] } UNMARK (aiHandle p) (aiHandle q)
    = cong aiHandle (funext-dep p q (λ st → irrCode h (p st) (q st)))

  irrCode : ∀ {s t st} (c : Code s t) (p q : AccCode s t c st) → p ≡ q
  irrCode ε trivial trivial = refl
  irrCode (i ◅ is) (step ai p) (step aj q) rewrite irrInstr i ai aj
    = cong _ (irrCode is p q)

Acc : ∀ {s t} → Code s t → Set
Acc c = ∀ st → AccCode _ _ c st

acc-cons : ∀ {s t u} (st : State s) (i : Instr s t) (is : Code t u)
  → (ai : AccInstr s t i st)
  → AccCode s u (i ◅ is) st
  → AccCode t u is (execInstr i st ai)
acc-cons st i is ai (step aj ac) rewrite irrInstr i ai aj = ac

acc-app : ∀ {s t v u st} (c : Code s (Val v ∷ Han v ∷ t)) (d : Code (Val v ∷ t) u)
  → AccCode _ _ c st → (∀ st' → AccCode _ _ d st') → AccCode _ _ (c ◅◅ UNMARK ◅ d) st
acc-app {.(Val v ∷ Han v ∷ t)} {t} {v} {u} { ✓[ x :: h !! st ] } ε d ac ad 
  = step aiUnmark✓ (ad ✓[ x :: st ])
acc-app {.(Val v ∷ Han v ∷ t)} {t} {v} {u} { ![ suc n , r ] } ε d ac ad 
  = step aiUnmark! (ad ![ n , r ])
acc-app {Val v ∷ Han .v ∷ t} .{t} .{v} {u} { ![ zero , Okay .{v} h st ] } ε d ac ad
  = step (aiHandle λ st' → {!!} ) (ad _)
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

term : ∀ {s t} → (c : Code s t) → Closed c → ∀ st → AccCode s t c st
term c pf = term' (fork c pf)
