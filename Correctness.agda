module Correctness where

open import Function using (_∘_; id)
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

compile-distr : ∀ {t u v} (code₁ : Code t u) (code₂ : Code u v) (st : Stack t)
  → execCode (code₁ ◅◅ code₂) st ≡ execCode code₂ (execCode code₁ st)
compile-distr ε        cs st = refl
compile-distr (i ◅ is) cs st = compile-distr is cs (execInstr i st)

correctness : ∀ {u s} (e : Exp u) (st : Stack s) → execCode (compile e) st ≡ denExp e :-: st
correctness (Lit x) _  = refl
correctness (f $ x) st = begin
  execCode (compile x ◅◅ compile f ◅◅ APPLY ◅ ε) st
    ≡⟨ compile-distr (compile x) _ _ ⟩
  execCode (compile f ◅◅ APPLY ◅ ε) (execCode (compile x) st)
    ≡⟨ compile-distr (compile f) _ _ ⟩
  (execCode ⟦ APPLY ⟧ ∘ execCode (compile f) ∘ execCode (compile x)) st
    ≡⟨ cong (λ z → (execCode ⟦ APPLY ⟧ ∘ execCode (compile f)) z) (correctness x _) ⟩
  (execCode ⟦ APPLY ⟧ ∘ execCode (compile f)) (denExp x :-: st)
    ≡⟨ cong (λ z → execCode ⟦ APPLY ⟧ z) (correctness f _)⟩
  execCode ⟦ APPLY ⟧ (denExp f :-: denExp x :-: st)
    ≡⟨ refl ⟩
  denExp f (denExp x) :-: st
    ∎
  where
    open ≡-Reasoning

