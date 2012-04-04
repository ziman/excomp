module Execution.Informative where

open import Function
open import Data.Nat
open import Data.Sum
open import Data.List
open import Data.Star
open import Data.Maybe
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import TypeUniverse
open import Expression
open import Denotation
open import Code
open import Execution.Utils

data State (s : Shape) : Set where
  ✓[_] : Stack s → State s
  ![_,_] : (n : ℕ) → Resume (unwindShape s n) (unwindHnd s n) → State s

mutual
  -- Accessibility of instructions (+ state)
  data AccInstr : ∀ s t → Instr s t → State s → Set where
    aiAdd : ∀ {s st} → AccInstr (Val Nat ∷ Val Nat ∷ s) (Val Nat ∷ s) ADD st
    aiPush : ∀ {s u x st} → AccInstr s (Val u ∷ s) (PUSH x) st
    aiThrow : ∀ {s u st} → AccInstr s (Val u ∷ s) THROW st
    aiMark : ∀ {s u st} {h : Code s (Val u ∷ s)} → AccInstr s (Han u ∷ s) (MARK h) st
    aiUnmark✓ : ∀ {s u st} → AccInstr (Val u ∷ Han u ∷ s) (Val u ∷ s) UNMARK ✓[ st ]
    aiUnmark! : ∀ {s u n r} → AccInstr (Val u ∷ Han u ∷ s) (Val u ∷ s) UNMARK ![ suc n , r ]
    aiHandle : ∀ {s u h st}
      → AccCode s (Val u ∷ s) h ✓[ st ]
      → AccInstr (Val u ∷ Han u ∷ s) (Val u ∷ s) UNMARK ![ zero , Okay h st ] 

  -- Accessibility of code (+ state)
  data AccCode : ∀ s t → Code s t → State s → Set where
    trivial : ∀ {s st} → AccCode s s ε st
    step : ∀ {s t u i is st}
      → (ai : AccInstr s t i st)
      → AccCode t u is (execInstr i st ai)
      → AccCode s u (i ◅ is) st

  -- Instruction execution
  execInstr : ∀ {s t} → (i : Instr s t) → (st : State s) → AccInstr s t i st → State t

  -- Normal operation
  execInstr ADD      ✓[ x :: y :: st ] aiAdd     = ✓[ (x + y) :: st ]
  execInstr UNMARK   ✓[ x :: _ !! st ] aiUnmark✓ = ✓[       x :: st ]
  execInstr (PUSH x) ✓[           st ] aiPush    = ✓[       x :: st ]
  execInstr (MARK h) ✓[           st ] aiMark    = ✓[       h !! st ]

  -- Exception throwing
  execInstr THROW ✓[ st ] aiThrow = ![ zero , unwindStack st zero  ]

  -- Non-trivial exception processing
  execInstr (MARK _) ![ n     , r         ] aiMark        = ![ suc n , r ]
  execInstr UNMARK   ![ suc n , r         ] aiUnmark!     = ![ n     , r ]
  execInstr UNMARK   ![ zero  , Okay h st ] (aiHandle ac) = execCode h ✓[ st ] ac

  -- Trivial exception processing: instruction skipping
  execInstr THROW    ![ n , r ] aiThrow = ![ n , r ]
  execInstr ADD      ![ n , r ] aiAdd   = ![ n , r ]
  execInstr (PUSH _) ![ n , r ] aiPush  = ![ n , r ]

  -- Code execution
  execCode : ∀ {s t} → (c : Code s t) → (st : State s) → AccCode s t c st → State t
  execCode ε        st trivial   = st
  execCode (i ◅ is) st (step ai ac) = execCode is (execInstr i st ai) ac

