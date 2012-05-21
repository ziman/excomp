module Code where

open import Function
open import Data.List
open import Data.Sum
open import Data.Maybe
open import Data.Star
open import Data.Product

open import TypeUniverse
open import Expression

infixr 5 _v'∷_ _h'∷_
data Shape' : List U → Set where
  nilShape' : Shape' []
  _v'∷_ : ∀ {us} (u : U) → Shape' us → Shape' us
  _h'∷_ : ∀ {us} (u : U) → (sh : Shape' us) → Shape' (u ∷ us)

Shape : Set
Shape = ∃ Shape'

infixr 5 _v∷_ _h∷_
_v∷_ : (u : U) → Shape → Shape
_v∷_ u (hs , sh) = hs , u v'∷ sh

_h∷_ : (u : U) → Shape → Shape
_h∷_ u (hs , sh) = u ∷ hs , u h'∷ sh

nilShape : Shape
nilShape = [] , nilShape'

mutual
  -- Instructions of the stack machine.
  data Instr : Shape → Shape → Set where
    PUSH : ∀ {u s} → el u → Instr s (u v∷ s)
    ADD : ∀ {s} → Instr (Nat v∷ Nat v∷ s) (Nat v∷ s)
    MARK : ∀ {u s} → Code s (u v∷ s) → Instr s (u h∷ s)
    UNMARK : ∀ {u s} → Instr (u v∷ u h∷ s) (u v∷ s)
    THROW : ∀ {u s} → Instr s (u v∷ s)

  -- Code is an (indexed) list of instructions.
  Code : Shape → Shape → Set
  Code = Star Instr

infixr 50 _::_
infixr 50 _!!_
data Stack : Shape → Set where
  snil : Stack nilShape
  _::_ : ∀ {u us sh} → el u → Stack (us , sh) → Stack (us , u v'∷ sh)
  _!!_ : ∀ {u us sh} → Code (us , sh) (us , u v'∷ sh) → Stack (us , sh) → Stack (u ∷ us , u h'∷ sh)

