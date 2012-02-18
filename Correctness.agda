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

exec-distr : ∀ {s r t} {code₁ : Code t r} {code₂ : Code s t} {st : Stack s} → exec (code₂ ∘ code₁) st ≡ (exec code₁ ∘ exec code₂) st
exec-distr {[]} {r} {t} {code₁} {code₂} {∅} = {!!}
exec-distr {p ∷ q} {r} {t} {code₁} {code₂} {x :: y} = {!!}

correctness : ∀ {u s} (e : Exp u) (st : Stack s) → exec (compile e) st ≡ denExp e :: st
correctness (Lit x)      _  = refl
correctness (Bin op l r) st = begin
    exec (compile (Bin op l r)) st
      ≡⟨ refl ⟩
    exec (compile r ∘ compile l ∘ _,,_ (opInstr op)) st
      ≡⟨ refl ⟩
    exec-seq (compile r (compile l (opInstr op ,, inil))) st
      ≡⟨ {!!} ⟩
    denExp (Bin op l r) :: st
      ∎
  where
    open ≡-Reasoning
