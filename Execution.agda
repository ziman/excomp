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
  ![_,_] : (n : ℕ) → Stack (unwindShape s n) → State s

exec : ∀ {s t} → Code s t → State s → State t
exec ε st = st

-- Normal operation
exec (PUSH x ◅ is) ✓[           st ] = exec is ✓[    x    :: st ]
exec (ADD    ◅ is) ✓[ x :: y :: st ] = exec is ✓[ (x + y) :: st ]
exec (MARK   ◅ is) ✓[           st ] = exec is ✓[        ■!! st ]
exec (UNMARK ◅ is)              st   = exec is               st
exec (THROW  ◅ is) ✓[           st ] = exec is ![ zero , unwindStack st zero ]

-- Exception handling: trivial
exec (THROW  ◅ is) ![     n , st ] = exec is ![     n , st ]
exec (PUSH x ◅ is) ![     n , st ] = exec is ![     n , st ]
exec (ADD    ◅ is) ![     n , st ] = exec is ![     n , st ]
exec (MARK   ◅ is) ![     n , st ] = exec is ![ suc n , st ]
exec (HANDLE ◅ is) ![ suc n , st ] = exec is ![     n , st ]

-- Exception handling: run the handler on exception
exec (HANDLE ◅ is) ![ zero , st ] = exec is ✓[ st ]

-- Exception handling: no exception, skip the handler
exec (HANDLE ◅ is) ✓[ x :: ■!! st ] = {!!}
