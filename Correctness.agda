module Correctness where

open import Function
open import Data.Nat
open import Data.List
open import Data.Star
open import Relation.Binary.PropositionalEquality

open import TypeUniverse
open import Expression
open import Denotation
open import Code
open import Compiler
open import Execution

-- Correctness of operator translation. Because of the way how the translation
-- is written, this is not "free" and must be proved for each operator.
op-correct : ∀ {s u v w} {st : Stack s} {x : el u} {y : el v} (op : Op u v w)
  → execInstr (opInstr op) (x :-: y :-: st) ≡ denOp op x y :-: st
op-correct Plus = refl

-- Exec distributes over ⊕.
compile-distr : ∀ {t u v} (code₁ : Code t u) (code₂ : Code u v) (st : Stack t)
  → execCode (code₁ ◅◅ code₂) st ≡ execCode code₂ (execCode code₁ st)
compile-distr ε cs st = refl
compile-distr (i ◅ is) cs st = compile-distr is cs _

-- The main correctness theorem: executing compiled code is equivalent
-- to pushing the correspondent denotation to the stack.
correctness : ∀ {u s} (e : Exp u) (st : Stack s) → execCode (compile e) st ≡ denExp e :-: st
correctness (Lit x)      _  = refl
correctness (Bin op l r) st = begin
    execCode (compile (Bin op l r)) st
      ≡⟨ refl ⟩
    execCode (compile r ◅◅ compile l ◅◅ ⟦ opInstr op ⟧) st
      ≡⟨ compile-distr (compile r) _ _ ⟩
    execCode (compile l ◅◅ ⟦ opInstr op ⟧) (execCode (compile r) st)
      ≡⟨ compile-distr (compile l) _ _ ⟩
    execCode ⟦ opInstr op ⟧ (execCode (compile l) (execCode (compile r) st))
      ≡⟨ cong (λ z → execCode ⟦ opInstr op ⟧ (execCode (compile l) z)) (correctness r st) ⟩
    execCode ⟦ opInstr op ⟧ (execCode (compile l) (denExp r :-: st))
      ≡⟨ cong (λ z → execCode ⟦ opInstr op ⟧ z) (correctness l (denExp r :-: st)) ⟩
    execCode ⟦ opInstr op ⟧ (denExp l :-: denExp r :-: st)
      ≡⟨ refl ⟩
    execInstr (opInstr op) (denExp l :-: denExp r :-: st)
      ≡⟨ op-correct op ⟩
    denOp op (denExp l) (denExp r) :-: st
      ≡⟨ refl ⟩
    denExp (Bin op l r) :-: st
      ∎
  where
    open ≡-Reasoning
