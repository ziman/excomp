module TypeUniverse where

open import Function
open import Data.Nat
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- Types available in the modelled language.
data U : Set where
  Nat : U
  _⇒_ : U → U → U

-- Interpretation of the types into Agda types.
el : U → Set
el Nat      = ℕ
el (x ⇒ y) = el x → el y

private
  eq-lemma₁ : ∀ {p q r s : U} → (p ⇒ q) ≡ (r ⇒ s) → p ≡ r
  eq-lemma₁ refl = refl

  eq-lemma₂ : ∀ {p q r s : U} → (p ⇒ q) ≡ (r ⇒ s) → q ≡ s
  eq-lemma₂ refl = refl

-- Equality of the types is decidable.
eqDecU : ∀ (x y : U) → Dec (x ≡ y)
eqDecU Nat Nat = yes refl
eqDecU (p ⇒ q) (r  ⇒ s) with eqDecU p r | eqDecU q s
eqDecU (p ⇒ q) (.p ⇒ .q) | yes refl | yes refl = yes refl
eqDecU (p ⇒ q) (r  ⇒ .q) | no  pfL  | yes refl = no (pfL ∘ eq-lemma₁)
eqDecU (p ⇒ q) (.p ⇒  s) | yes refl | no  pfR  = no (pfR ∘ eq-lemma₂)
eqDecU (p ⇒ q) (r  ⇒  s) | no  pfL  | no  pfR  = no (pfL ∘ eq-lemma₁)
eqDecU Nat (_ ⇒ _) = no (λ ())
eqDecU (_ ⇒ _) Nat = no (λ ())
