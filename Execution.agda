module Execution where

open import Data.Nat
open import Data.List
open import Data.Star
open import Data.Maybe

open import TypeUniverse
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
  ×[_,_] : (n : ℕ) → Resume (unwindShape s n) (unwindHnd s n) → State s

mutual
  -- Instruction execution
  execInstr : ∀ {s t} → Instr s t → State s → State t
  
  -- Normal operation
  execInstr ADD      ✓[ x :: y :: st ] = ✓[ (x + y) :: st ]
  execInstr UNMARK   ✓[ x :: _ !! st ] = ✓[       x :: st ]
  execInstr (PUSH x) ✓[           st ] = ✓[       x :: st ]
  execInstr (MARK h) ✓[           st ] = ✓[       h !! st ]

  -- Exception throwing
  -- Unwind the stack, creating a resumption point. Instruction skipping begins.
  execInstr THROW ✓[ st ] = ×[ zero , unwindStack st zero  ]

  -- Non-trivial exception processing
  execInstr (MARK _) ×[ n     , r         ] = ×[ suc n , r ]
  execInstr UNMARK   ×[ suc n , r         ] = ×[ n     , r ]
  execInstr UNMARK   ×[ zero  , Okay h st ] = execCode h ✓[ st ]

  -- Trivial exception processing: instruction skipping
  execInstr THROW    ×[ n , r ] = ×[ n , r ]
  execInstr ADD      ×[ n , r ] = ×[ n , r ]
  execInstr (PUSH _) ×[ n , r ] = ×[ n , r ]

  -- Code execution
  -- This is a left fold over instructions.
  execCode : ∀ {s t} → Code s t → State s → State t
  execCode ε        st = st
  execCode (i ◅ is) st = execCode is (execInstr i st)


