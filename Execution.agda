module Execution where

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

-- Get the type of the top-most handler in the Shape.
unwindHnd : Shape → ℕ → Maybe U
unwindHnd (Han u ∷ xs) zero    = just u
unwindHnd (Han _ ∷ xs) (suc n) = unwindHnd xs n
unwindHnd (Val _ ∷ xs) n       = unwindHnd xs n
unwindHnd []           _       = nothing

-- Unwind the shape up to just below the top-most handler.
unwindShape : Shape → ℕ → Shape
unwindShape (Han _ ∷ xs) zero    = xs
unwindShape (Han _ ∷ xs) (suc n) = unwindShape xs n
unwindShape (Val _ ∷ xs) n       = unwindShape xs n
unwindShape []           _       = []

-- Normal operation resumption point.
data Resume (s : Shape) : Maybe U → Set where
  -- A handler is available, also remember the stack on which the handler should operate.
  Okay : ∀ {u} → Code s (Val u ∷ s) → Stack s → Resume s (just u)
  -- Uncaught throw.
  Fail : Resume s nothing

-- Unwind the stack up to just below the top-most handler.
unwindStack : ∀ {s} → Stack s → (n : ℕ) → Resume (unwindShape s n) (unwindHnd s n)
unwindStack (h !! xs) zero    = Okay h xs
unwindStack (_ !! xs) (suc n) = unwindStack xs n
unwindStack (_ :: xs) n       = unwindStack xs n
unwindStack snil      _       = Fail

-- Execution state of the virtual machine.
data State (s : Shape) : Set where
  -- Normal operation: plain old stack.
  ✓[_] : Stack s → State s
  -- Exceptional state: skip instructions until the corresponding UNMARK and then resume.
  ![_,_] : (n : ℕ) → Resume (unwindShape s n) (unwindHnd s n) → State s

mutual
  measureInstr : ∀ {s t} → Instr s t → ℕ
  measureInstr (PUSH x) = 1
  measureInstr  ADD     = 1
  measureInstr (MARK x) = 1 + measureCode x
  measureInstr  UNMARK  = 1
  measureInstr  THROW   = 1

  measureCode : ∀ {s t} → Code s t → ℕ
  measureCode ε        = 0
  measureCode (i ◅ is) = measureInstr i + measureCode is

  measureState : ∀ {s} → State s → ℕ
  measureState ✓[ st ] = 0
  measureState {s} ![ n , y ] with unwindHnd s n
  measureState {s} ![ n , Okay h st ] | just u  = measureCode h
  measureState {s} ![ n , Fail      ] | nothing = 0

mutual
  -- Instruction execution
  execInstr : ∀ {s t}
    → (i : Instr s t) → (st : State s)
    → (m : ℕ) → m ≡ measureInstr i + measureState st
    → State t
  
  -- Normal operation
  execInstr ADD      ✓[ x :: y :: st ] _ _ = ✓[ (x + y) :: st ]
  execInstr UNMARK   ✓[ x :: _ !! st ] _ _ = ✓[       x :: st ]
  execInstr (PUSH x) ✓[           st ] _ _ = ✓[       x :: st ]
  execInstr (MARK h) ✓[           st ] _ _ = ✓[       h !! st ]

  -- Exception throwing
  -- Unwind the stack, creating a resumption point. Instruction skipping begins.
  execInstr THROW ✓[ st ] _ _ = ![ zero , unwindStack st zero  ]

  -- Non-trivial exception processing
  execInstr (MARK _) ![ n     , r         ] _ _ = ![ suc n , r ]
  execInstr UNMARK   ![ suc n , r         ] _ _ = ![ n     , r ]

  -- Exception handling
  execInstr UNMARK ![ zero , Okay h st ] m pf = execCode h ✓[ st ] {!!} {!!}

  -- Trivial exception processing: instruction skipping
  execInstr THROW    ![ n , r ] _ _ = ![ n , r ]
  execInstr ADD      ![ n , r ] _ _ = ![ n , r ]
  execInstr (PUSH _) ![ n , r ] _ _ = ![ n , r ]

  -- Code execution
  -- This is a left fold over instructions.
  execCode : ∀ {s t}
    → (c : Code s t) → (st : State s)
    → (m : ℕ) → m ≡ measureCode c + measureState st
    → State t
  execCode ε        st _ _  = st
  execCode (i ◅ is) st m pf = execCode is (execInstr i st {!!} {!!}) {!!} {!!}


