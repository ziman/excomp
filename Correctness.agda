module Correctness where

open import Function
open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Star
open import Relation.Binary.PropositionalEquality

open import TypeUniverse
open import Expression
open import Denotation
open import Code
open import Compiler
open import Execution


module Utils where
  open Execution.MachineState public

  -- Smart stack pusher
  infixr 5 _:::_
  _:::_ : ∀ {u s} → Maybe (el u) → State s → State (Val u ∷ s)
  _:::_ nothing  ×[ n , st ] = ×[ n , st ]
  _:::_ (just x) ×[ n , st ] = ×[ n , st ]
  _:::_ nothing  ![ n , st ] = ![ n , st ]
  _:::_ (just x) ![ n , st ] = ![ n , st ]
  _:::_ nothing  ✓[     st ] = ×[ zero , unwindStack st zero ]
  _:::_ (just x) ✓[     st ] = ✓[ x :: st ]

  -- Execution distributes over ◅◅
  distr : ∀ {s t u} (st : State s) (c : Code s t) (d : Code t u)
    → execCode (c ◅◅ d) st ≡ execCode d (execCode c st)
  distr st ε d = refl
  distr st (i ◅ is) d = distr _ is d

open Utils

-- Central case analysis for binary operators
lemma-op : ∀ {s t u v} (r : Exp t) (l : Exp u) (op : Op u t v) (st : State s)
  → execInstr (opInstr op) (denExp l ::: denExp r ::: st) ≡ denExp (Bin op l r) ::: st
lemma-op r l op st with denExp l | denExp r
lemma-op r l Plus ✓[ st ] | just x  | just y  = refl
lemma-op r l Plus ✓[ st ] | just x  | nothing = refl
lemma-op r l Plus ✓[ st ] | nothing | just y  = refl
lemma-op r l Plus ✓[ st ] | nothing | nothing = refl
lemma-op r l Plus ×[ n , st ] | just x  | just y  = refl
lemma-op r l Plus ×[ n , st ] | just x  | nothing = refl
lemma-op r l Plus ×[ n , st ] | nothing | just y  = refl
lemma-op r l Plus ×[ n , st ] | nothing | nothing = refl
lemma-op r l Plus ![ n , st ] | just x  | just y  = refl
lemma-op r l Plus ![ n , st ] | just x  | nothing = refl
lemma-op r l Plus ![ n , st ] | nothing | just y  = refl
lemma-op r l Plus ![ n , st ] | nothing | nothing = refl

-- Central case analysis for catch-blocks
lemma-catch : ∀ {u s} (e h : Exp u) (st : State s)
  → execInstr UNMARK (denExp h ::: execInstr HANDLE (denExp e ::: execInstr MARK st))
    ≡ denExp (Catch e h) ::: st
lemma-catch e h st with denExp e
lemma-catch e h st | just x with denExp h
lemma-catch e h ✓[ st ] | just x | just y = refl
lemma-catch e h ✓[ st ] | just x | nothing = refl
lemma-catch e h ×[ n , st ] | just x | just y = refl
lemma-catch e h ×[ n , st ] | just x | nothing = refl
lemma-catch e h ![ n , st ] | just x | just y = refl
lemma-catch e h ![ n , st ] | just x | nothing = refl
lemma-catch e h st | nothing with denExp h
lemma-catch e h ✓[ st ] | nothing | just x = refl
lemma-catch e h ✓[ st ] | nothing | nothing = refl
lemma-catch e h ×[ n , st ] | nothing | just x = refl
lemma-catch e h ×[ n , st ] | nothing | nothing = refl
lemma-catch e h ![ n , st ] | nothing | just x = refl
lemma-catch e h ![ n , st ] | nothing | nothing = refl

-- ** The main correctness theorem **
correctness : ∀ {u} (e : Exp u) {s : Shape} (st : State s)
  → execCode (compile e) st ≡ (denExp e ::: st)

-- Trivial expressions
correctness Throw   ✓[     st ] = refl
correctness Throw   ×[ n , st ] = refl
correctness Throw   ![ n , st ] = refl
correctness (Lit x) ✓[     st ] = refl
correctness (Lit x) ×[ n , st ] = refl
correctness (Lit x) ![ n , st ] = refl

-- Catch-expressions
correctness (Catch e h) st  = let open ≡-Reasoning in begin
  execCode (MARK ◅ compile e ◅◅ HANDLE ◅ compile h ◅◅ UNMARK ◅ ε) st
    ≡⟨ distr _ (compile e) _ ⟩
  execCode (compile h ◅◅ UNMARK ◅ ε) ((execInstr HANDLE ∘ execCode (compile e) ∘ execInstr MARK) st)
    ≡⟨ distr _ (compile h) _ ⟩
  (execInstr UNMARK ∘ execCode (compile h) ∘ execInstr HANDLE ∘ execCode (compile e) ∘ execInstr MARK $ st)
    ≡⟨ cong (execInstr UNMARK ∘ execCode (compile h) ∘ execInstr HANDLE) (correctness e _) ⟩
  (execInstr UNMARK ∘ execCode (compile h) ∘ execInstr HANDLE) (denExp e ::: execInstr MARK st)
    ≡⟨ cong (execInstr UNMARK) (correctness h _) ⟩
  execInstr UNMARK (denExp h ::: execInstr HANDLE (denExp e ::: execInstr MARK st))
    ≡⟨ lemma-catch e h st ⟩
  denExp (Catch e h) ::: st
    ∎

-- Binary operator expressions
correctness (Bin op l r) st = let open ≡-Reasoning in begin
  execCode (compile r ◅◅ compile l ◅◅ opInstr op ◅ ε) st
    ≡⟨ distr _ (compile r) _ ⟩
  execCode (compile l ◅◅ opInstr op ◅ ε) (execCode (compile r) st)
    ≡⟨ distr _ (compile l) _ ⟩
  execCode (opInstr op ◅ ε) (execCode (compile l) (execCode (compile r) st))
    ≡⟨ refl ⟩
  execInstr (opInstr op) (execCode (compile l) (execCode (compile r) st)) 
    ≡⟨ cong (λ x → execInstr (opInstr op) (execCode (compile l) x)) (correctness r st) ⟩
  execInstr (opInstr op) (execCode (compile l) (denExp r ::: st))
    ≡⟨ cong (λ x → execInstr (opInstr op) x) (correctness l (denExp r ::: st)) ⟩
  execInstr (opInstr op) (denExp l ::: denExp r ::: st)
    ≡⟨ lemma-op r l op st ⟩
  denExp (Bin op l r) ::: st
    ∎

