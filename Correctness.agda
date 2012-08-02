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

-- Smart stack pusher
infixr 5 _:::_
_:::_ : ∀ {u s} → Maybe (el u) → State s → State (Val u ∷ s)
_:::_ nothing  ×[ n , st ] = ×[ n , st ]
_:::_ (just x) ×[ n , st ] = ×[ n , st ]
_:::_ nothing  ✓[   st   ] = ×[ zero , unwindStack st zero ]
_:::_ (just x) ✓[   st   ] = ✓[ x :: st ]

-- Execution distributes over ◅◅
distr : ∀ {s t u} (st : State s) (c : Code s t) (d : Code t u)
  → execCode (c ◅◅ d) st ≡ execCode d (execCode c st)
distr st ε d = refl
distr st (x ◅ xs) d rewrite distr (execInstr x st) xs d = refl

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

-- Central case analysis for exception handlers
lemma-catch : ∀ {s u} (e : Exp u) (h : Exp u) (st : State s)
  → (∀ {s} (st' : State s) → execCode (compile h) st' ≡ denExp h ::: st')
  → execInstr (UNMARK (compile h)) (denExp e ::: execInstr MARK st) ≡ denExp (Catch e h) ::: st
lemma-catch e h st pf with denExp e
lemma-catch e h ✓[ st ] pf | just x = refl
lemma-catch e h ×[ n , st ] pf | just x = refl
lemma-catch e h ✓[ st ] pf | nothing with denExp h
lemma-catch e h ✓[ st ] pf | nothing | just x  = pf ✓[ st ]
lemma-catch e h ✓[ st ] pf | nothing | nothing = pf ✓[ st ]
lemma-catch e h ×[ n , st ] pf | nothing with denExp h
lemma-catch e h ×[ n , st ] pf | nothing | just x  = refl
lemma-catch e h ×[ n , st ] pf | nothing | nothing = refl

-- ** The main correctness theorem **
correctness : ∀ {u} (e : Exp u) {s : Shape} (st : State s)
  → execCode (compile e) st ≡ (denExp e ::: st)

-- Trivial cases
correctness Throw ✓[ st ] = refl
correctness Throw ×[ n , st ] = refl
correctness (Lit x) ✓[ st ] = refl
correctness (Lit x) ×[ n , st ] = refl

-- Binary operators
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

-- Exception handling
correctness (Catch e h) st = let open ≡-Reasoning in begin
  execCode (compile e ◅◅ UNMARK (compile h) ◅ ε) (execInstr MARK st)
    ≡⟨ distr _ (compile e) _ ⟩
  execInstr (UNMARK (compile h)) (execCode (compile e) (execInstr MARK st))
    ≡⟨ cong (λ x → execInstr (UNMARK (compile h)) x) (correctness e _) ⟩
  execInstr (UNMARK (compile h)) (denExp e ::: execInstr MARK st)
    ≡⟨ lemma-catch e h st (correctness h) ⟩
  denExp (Catch e h) ::: st
    ∎

