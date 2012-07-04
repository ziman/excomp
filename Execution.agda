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

module MachineState where
  -- Unwind the shape up to just below the n-th handle-mark from the top.
  unwindShape : Shape → ℕ → Shape
  unwindShape (Han _ ∷ xs)  zero   = xs
  unwindShape (Han _ ∷ xs) (suc n) = unwindShape xs n
  unwindShape (Skp _ ∷ xs)  n      = unwindShape xs n
  unwindShape (Val _ ∷ xs)  n      = unwindShape xs n
  unwindShape []            _      = []

  -- Shape of the stack after skipping the n-th skip-mark from the top.
  skipShape : Shape → ℕ → Shape
  skipShape (Han _ ∷ xs)  n      = skipShape xs n
  skipShape (Skp u ∷ xs)  zero   = Val u ∷ xs
  skipShape (Skp _ ∷ xs) (suc n) = skipShape xs n
  skipShape (Val _ ∷ xs)  n      = skipShape xs n
  skipShape []            _      = []

  -- Unwind the stack up to just below the n-th handle-mark from the top.
  unwindStack : ∀ {s} → Stack s → (n : ℕ) → Stack (unwindShape s n)
  unwindStack (han _ :: xs)  zero   = xs
  unwindStack (han _ :: xs) (suc n) = unwindStack xs n
  unwindStack (skp _ :: xs)  n      = unwindStack xs n
  unwindStack (    _ :: xs)  n      = unwindStack xs n
  unwindStack  snil          _      = snil

  -- Execution state of the virtual machine.
  data State (s : Shape) : Set where
    -- Normal operation
    ✓[_] : (st : Stack s) → State s
    -- Exceptional state
    ![_,_] : (n : ℕ) → (st : Stack (unwindShape s n)) → State s
    -- Handler skipping (forward jump)
    ×[_,_] : (n : ℕ) → (st : Stack (skipShape s n)) → State s

open MachineState

-- Instruction execution
execInstr : ∀ {s t} → Instr s t → State s → State t

-- Normal operation
execInstr (PUSH  x ) ✓[           st ] = ✓[    x    :: st ]
execInstr  ADD       ✓[ x :: y :: st ] = ✓[ (x + y) :: st ]
execInstr (MARK {u}) ✓[           st ] = ✓[ han u :: skp u :: st ]
execInstr  THROW     ✓[           st ] = ![ zero , unwindStack st zero ]
execInstr  UNMARK    ✓[ x :: skp u :: st ] = ✓[    x    :: st ]
  
-- Exception handling: trivial
execInstr  THROW   ![     n , st ] = ![     n , st ]
execInstr (PUSH x) ![     n , st ] = ![     n , st ]
execInstr  ADD     ![     n , st ] = ![     n , st ]
execInstr  UNMARK  ![     n , st ] = ![     n , st ]
execInstr  MARK    ![     n , st ] = ![ suc n , st ]
execInstr  HANDLE  ![ suc n , st ] = ![     n , st ]
  
-- Forward jump: trivial
execInstr  THROW   ×[ n , st ] = ×[ n , st ]
execInstr (PUSH x) ×[ n , st ] = ×[ n , st ]
execInstr  ADD     ×[ n , st ] = ×[ n , st ]
execInstr  HANDLE  ×[ n , st ] = ×[ n , st ]
execInstr  MARK    ×[ n , st ] = ×[ suc n , st ]
execInstr  UNMARK  ×[ suc n , st ] = ×[ n , st ]
execInstr  UNMARK  ×[ zero  , st ] = ✓[ st ]
  
-- Exception handling: run the handler on exception
execInstr HANDLE ![ zero , st ] = ✓[ st ]
  
-- Exception handling: no exception, skip the handler, keeping the current stack
execInstr HANDLE ✓[ x :: han u :: skp .u :: st ] = ×[ zero , x :: st ]

-- Execution of code is nothing more than a left fold
execCode : ∀ {s t} → Code s t → State s → State t
execCode ε st = st
execCode (i ◅ is) st = execCode is (execInstr i st)
