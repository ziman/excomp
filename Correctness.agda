module Correctness where

open import Function
open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality

open import TypeUniverse
open import Expression
open import Denotation
open import Code
open import Compiler
open import Execution

compile-distr : ∀ {t u v} (code₁ : Code t u) (code₂ : Code u v) (st : Stack t)
  → exec (code₁ ⊕ code₂) st ≡ exec code₂ (exec code₁ st)
compile-distr cnil      code₂ st = refl
compile-distr (i ,, is) code₂ st = begin
    exec ((i ,, is) ⊕ code₂) st
      ≡⟨ {!!} ⟩
    exec code₂ (exec (i ,, is) st)
      ∎
  where
    open ≡-Reasoning

correctness : ∀ {u s} (e : Exp u) (st : Stack s) → exec (compile e) st ≡ denExp e :: st
correctness (Lit x)      _  = refl
correctness (Bin op l r) st = begin
    exec (compile (Bin op l r)) st
      ≡⟨ refl ⟩
    exec (compile r ⊕ compile l ⊕ single (opInstr op)) st
      ≡⟨ {!!} ⟩
    denExp (Bin op l r) :: st
      ∎
  where
    open ≡-Reasoning
