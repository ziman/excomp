module Execution where

open import Data.Nat
open import Data.List
open import Data.Star

open import Code

-- Unwind the shape up to just below the top-most handler.
unwindShape : Shape → ℕ → Shape
unwindShape (Han _ ∷ xs) zero    = xs
unwindShape (Han _ ∷ xs) (suc n) = unwindShape xs n
unwindShape (Val _ ∷ xs) n       = unwindShape xs n
unwindShape []           _       = []

-- Unwind the stack up to just below the top-most handler.
unwindStack : ∀ {s} → Stack s → (n : ℕ) → Stack (unwindShape s n)
unwindStack ( ■!! xs) zero    = xs
unwindStack ( ■!! xs) (suc n) = unwindStack xs n
unwindStack (_ :: xs) n       = unwindStack xs n
unwindStack snil      _       = snil

-- Execution state of the virtual machine.
data State (s : Shape) : Set where
  -- Normal operation: plain old stack.
  ✓[_] : Stack s → State s
  -- Exceptional state: skip instructions until the corresponding UNMARK and then resume.
  ×[_,_] : (n : ℕ) → Stack (unwindShape s n) → State s

mutual
  -- Instruction execution
  execInstr : ∀ {s t} → Instr s t → State s → State t
  
  -- Normal operation
  execInstr ADD        ✓[ x :: y :: st ] = ✓[ (x + y) :: st ]
  execInstr (UNMARK _) ✓[ x ::  ■!! st ] = ✓[       x :: st ]
  execInstr (PUSH x)   ✓[           st ] = ✓[       x :: st ]
  execInstr MARK       ✓[           st ] = ✓[        ■!! st ]

  -- Exception throwing
  -- Unwind the stack, creating a resumption point. Instruction skipping begins.
  execInstr THROW ✓[ st ] = ×[ zero , unwindStack st zero  ]

  -- Non-trivial exception processing
  execInstr MARK       ×[ n     , st ] = ×[ suc n , st ]
  execInstr (UNMARK _) ×[ suc n , st ] = ×[ n     , st ]
  execInstr (UNMARK h) ×[ zero  , st ] = execCode h ✓[ st ]

  -- Trivial exception processing: instruction skipping
  execInstr THROW    ×[ n , st ] = ×[ n , st ]
  execInstr ADD      ×[ n , st ] = ×[ n , st ]
  execInstr (PUSH _) ×[ n , st ] = ×[ n , st ]

  -- Code execution
  -- This is a left fold over instructions.
  execCode : ∀ {s t} → Code s t → State s → State t
  execCode ε        st = st
  execCode (i ◅ is) st = execCode is (execInstr i st)


