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

-- Unwind the shape up to just below the n-th handle-mark from the top.
unwindShape : Shape → ℕ → Shape
unwindShape (Han _ ∷ xs)  zero   = xs
unwindShape (Han _ ∷ xs) (suc n) = unwindShape xs n
unwindShape (Skp _ ∷ xs)  n      = unwindShape xs n
unwindShape (Val _ ∷ xs)  n      = unwindShape xs n
unwindShape []            _      = []

-- Unwind the stack up to just below the n-th handle-mark from the top.
unwindStack : ∀ {s} → Stack s → (n : ℕ) → Stack (unwindShape s n)
unwindStack (han _ :: xs)  zero   = xs
unwindStack (han _ :: xs) (suc n) = unwindStack xs n
unwindStack (skp _ :: xs)  n      = unwindStack xs n
unwindStack (    _ :: xs)  n      = unwindStack xs n
unwindStack  snil          _      = snil

-- Shape of the stack after skipping the n-th handler from the top.
skipShape : Shape → ℕ → Shape
skipShape (Han _ ∷ xs)  n      = skipShape xs n
skipShape (Skp u ∷ xs)  zero   = Val u ∷ xs
skipShape (Skp _ ∷ xs) (suc n) = skipShape xs n
skipShape (Val _ ∷ xs)  n      = skipShape xs n
skipShape []            _      = []

-- Execution state of the virtual machine.
data State (s : Shape) : Set where
  -- Normal operation
  ✓[_] : Stack s → State s
  -- Exceptional state
  ![_,_] : (n : ℕ) → Stack (unwindShape s n) → State s
  -- Handler skipping (forward jump)
  ×[_,_,_] : (u : U) → (n : ℕ) → Stack (skipShape s n) → State s

exec : ∀ {s t} → Code s t → State s → State t
exec ε st = st

-- Normal operation
exec (PUSH x ◅ is) ✓[           st ] = exec is ✓[    x    :: st ]
exec (ADD    ◅ is) ✓[ x :: y :: st ] = exec is ✓[ (x + y) :: st ]
exec (MARK{u}◅ is) ✓[           st ] = exec is ✓[ han u :: skp u :: st ]
exec (UNMARK ◅ is) ✓[ x :: skp u :: st ] = exec is ✓[    x    :: st ]
exec (THROW  ◅ is) ✓[           st ] = exec is ![ zero , unwindStack st zero ]

-- Exception handling: trivial
exec (THROW  ◅ is) ![     n , st ] = exec is ![     n , st ]
exec (PUSH x ◅ is) ![     n , st ] = exec is ![     n , st ]
exec (ADD    ◅ is) ![     n , st ] = exec is ![     n , st ]
exec (UNMARK ◅ is) ![     n , st ] = exec is ![     n , st ]
exec (MARK   ◅ is) ![     n , st ] = exec is ![ suc n , st ]
exec (HANDLE ◅ is) ![ suc n , st ] = exec is ![     n , st ]

-- Forward jump: trivial
exec (THROW  ◅ is) ×[ u , n , st ] = exec is ×[ u , n , st ]
exec (PUSH x ◅ is) ×[ u , n , st ] = exec is ×[ u , n , st ]
exec (ADD    ◅ is) ×[ u , n , st ] = exec is ×[ u , n , st ]
exec (HANDLE ◅ is) ×[ u , n , st ] = exec is ×[ u , n , st ]
exec (MARK   ◅ is) ×[ u , n , st ] = exec is ×[ u , suc n , st ]
exec (UNMARK ◅ is) ×[ u , suc n , st ] = exec is ×[ u , n , st ]
exec (UNMARK ◅ is) ×[ u , zero  , st ] = exec is ✓[ st ]

-- Exception handling: run the handler on exception
exec (HANDLE ◅ is) ![ zero , st ] = exec is ✓[ st ]

-- Exception handling: no exception, skip the handler, keeping the current stack
exec (HANDLE ◅ is) ✓[ x :: han u :: skp .u :: st ] = exec is ×[ u , zero , x :: st ]
