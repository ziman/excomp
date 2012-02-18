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

-- Correctness of operator translation. Because of the way how the translation
-- is written, this is not "free" and must be proved for each operator.
op-correct : ∀ {u v w q st} {x : el u} {y : el v} (op : Op u v w)
  → exec-instr (opInstr {u} {v} {w} {q} op) (x :: y :: st) ≡ denOp op x y :: st
op-correct Plus = refl

-- Exec distributes over ⊕.
compile-distr : ∀ {t u v} (code₁ : Code t u) (code₂ : Code u v) (st : Stack t)
  → exec (code₁ ⊕ code₂) st ≡ exec code₂ (exec code₁ st)
compile-distr cnil      cs st = refl
compile-distr (i ,, is) cs st = begin
    exec ((i ,, is) ⊕ cs) st
      ≡⟨ refl ⟩
    exec (is ⊕ cs) (exec-instr i st)
      ≡⟨ compile-distr is cs _ ⟩
    exec cs (exec is (exec-instr i st))
      ≡⟨ refl ⟩
    exec cs (exec (i ,, is) st)
      ∎
  where
    open ≡-Reasoning

-- The main correctness theorem: executing compiled code is equivalent
-- to pushing the correspondent denotation to the stack.
correctness : ∀ {u s} (e : Exp u) (st : Stack s) → exec (compile e) st ≡ denExp e :: st
correctness (Lit x)      _  = refl
correctness (Bin op l r) st = begin
    exec (compile (Bin op l r)) st
      ≡⟨ refl ⟩
    exec (compile r ⊕ compile l ⊕ single (opInstr op)) st
      ≡⟨ compile-distr (compile r) (compile l ⊕ single (opInstr op)) st ⟩
    exec (compile l ⊕ single (opInstr op)) (exec (compile r) st)
      ≡⟨ compile-distr (compile l) (single (opInstr op)) _ ⟩
    exec (single (opInstr op)) (exec (compile l) (exec (compile r) st))
      ≡⟨ cong (λ z → exec (single (opInstr op)) (exec (compile l) z)) (correctness r st) ⟩
    exec (single (opInstr op)) (exec (compile l) (denExp r :: st))
      ≡⟨ cong (λ z → exec (single (opInstr op)) z) (correctness l (denExp r :: st)) ⟩
    exec (single (opInstr op)) (denExp l :: denExp r :: st)
      ≡⟨ refl ⟩
    exec-instr (opInstr op) (denExp l :: denExp r :: st)
      ≡⟨ op-correct op ⟩
    denOp op (denExp l) (denExp r) :: st
      ≡⟨ refl ⟩
    denExp (Bin op l r) :: st
      ∎
  where
    open ≡-Reasoning
