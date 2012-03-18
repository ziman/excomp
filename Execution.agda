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
  -- Instruction execution
  execInstr : ∀ {s t} → Instr s t → State s → State t
  
  -- Normal operation
  execInstr ADD      ✓[ x :: y :: st ] = ✓[ (x + y) :: st ]
  execInstr UNMARK   ✓[ x :: _ !! st ] = ✓[       x :: st ]
  execInstr (PUSH x) ✓[           st ] = ✓[       x :: st ]
  execInstr (MARK h) ✓[           st ] = ✓[       h !! st ]

  -- Exception throwing
  execInstr THROW ✓[ st ] = ![ zero , unwindStack st zero  ]

  -- Non-trivial exception processing
  execInstr (MARK _) ![ n     , r         ] = ![ suc n , r ]
  execInstr UNMARK   ![ suc n , r         ] = ![ n     , r ]
  execInstr UNMARK   ![ zero  , Okay h st ] = execCode h ✓[ st ]

  -- Trivial exception processing: instruction skipping
  execInstr THROW    ![ n , r ] = ![ n , r ]
  execInstr ADD      ![ n , r ] = ![ n , r ]
  execInstr (PUSH _) ![ n , r ] = ![ n , r ]

  -- Code execution
  execCode : ∀ {s t} → Code s t → State s → State t
  execCode ε        st = st
  execCode (i ◅ is) st = execCode is (execInstr i st)


