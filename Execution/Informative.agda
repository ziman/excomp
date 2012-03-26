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

unwindHnd : Shape → ℕ → Maybe U
unwindHnd (Han u ∷ xs) zero    = just u
unwindHnd (Han _ ∷ xs) (suc n) = unwindHnd xs n
unwindHnd (Val _ ∷ xs) n       = unwindHnd xs n
unwindHnd []           _       = nothing

unwindShape : Shape → ℕ → Shape
unwindShape (Han _ ∷ xs) zero    = xs
unwindShape (Han _ ∷ xs) (suc n) = unwindShape xs n
unwindShape (Val _ ∷ xs) n       = unwindShape xs n
unwindShape []           _       = []

data Resume (s : Shape) : Maybe U → Set where
  Okay : ∀ {u} → Code s (Val u ∷ s) → Stack s → Resume s (just u)
  Fail : Resume s nothing

unwindStack : ∀ {s} → Stack s → (n : ℕ) → Resume (unwindShape s n) (unwindHnd s n)
unwindStack (h !! xs) zero    = Okay h xs
unwindStack (_ !! xs) (suc n) = unwindStack xs n
unwindStack (_ :: xs) n       = unwindStack xs n
unwindStack snil      _       = Fail

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

