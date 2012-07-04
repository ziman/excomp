module Code where

open import Function
open import Data.List
open import Data.Sum
open import Data.Maybe
open import Data.Star
open import Data.Unit

open import TypeUniverse
open import Expression

-- Stack items.
data Item : Set where
  Val : U → Item
  Han : U → Item
  Skp : U → Item

-- Shape of the stack.
Shape : Set
Shape = List Item

-- Instructions of the stack machine.
data Instr : Shape → Shape → Set where
  PUSH : ∀ {u s} → el u → Instr s (Val u ∷ s)
  ADD : ∀ {s} → Instr (Val nat ∷ Val nat ∷ s) (Val nat ∷ s)
  AND : ∀ {s} → Instr (Val bool ∷ Val bool ∷ s) (Val bool ∷ s)
  LEQ : ∀ {s} → Instr (Val nat ∷ Val nat ∷ s) (Val bool ∷ s)
  MARK : ∀ {u s} → Instr s (Han u ∷ Skp u ∷ s)
  HANDLE : ∀ {u s} → Instr (Val u ∷ Han u ∷ Skp u ∷ s) (Skp u ∷ s)
  UNMARK : ∀ {u s} → Instr (Val u ∷ Skp u ∷ s) (Val u ∷ s) 
  THROW : ∀ {u s} → Instr s (Val u ∷ s)

-- Code is an (indexed) list of instructions.
Code : Shape → Shape → Set
Code = Star Instr

infixr 50 _::_ han::_ skp::_
data Stack : Shape → Set where
  snil : Stack []
  _::_ : ∀ {u s} → el u → Stack s → Stack (Val u ∷ s)
  han::_ : ∀ {s} → {u : U} → Stack s → Stack (Han u ∷ s)
  skp::_ : ∀ {s} → {u : U} → Stack s → Stack (Skp u ∷ s)

