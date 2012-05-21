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

unwindHnd : List U → ℕ → List U
unwindHnd []        n      = []
unwindHnd (_ ∷ xs)  zero   = xs
unwindHnd (_ ∷ xs) (suc n) = unwindHnd xs n

unwindShape : ∀ us → Shape' us → (n : ℕ) → Shape' (unwindHnd us n)
unwindShape      []          xs       n  = nilShape'
unwindShape (u ∷ us) (.u h'∷ xs)   zero  = xs
unwindShape      us  (_  v'∷ xs)      n  = unwindShape us xs n
unwindShape (u ∷ us) (.u h'∷ xs) (suc n) = unwindShape us xs n

-- Unwind the stack up to just below the top-most handler.
unwindStack : ∀ {u : U} {us : List U} {s : Shape' (u ∷ us)}
  → Stack (u ∷ us , s)
  → (n : ℕ)
  → Stack (unwindHnd (u ∷ us) n , unwindShape (u ∷ us) s n)
unwindStack {u} {    us} {.u h'∷ sh} (h !! xs)   zero  = xs
unwindStack {u} {v ∷ us} {.u h'∷ sh} (h !! xs) (suc n) = unwindStack xs n
unwindStack {u} {    []} {.u h'∷ sh} (h !! xs) (suc n) = snil
unwindStack {u} {    us} { v v'∷ sh} (x :: xs)      n  = unwindStack xs n

{-
-- Execution state of the virtual machine.
data State : Shape → Set where
  -- Normal operation: plain old stack.
  ✓[_] : ∀ {s} → Stack s → State s
  -- Caught exception.
  ![_,_,_] : (n : ℕ) {u : U} {us : List U} {s' : Shape' us}
    → let s = us , s' in
      Code s (u v∷ s) → Stack s → State s
  -- Uncaught exception.
  ×[] : ∀ {s} → State ([] , s)

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
  -- This is a left fold over instructions.
  execCode : ∀ {s t} → Code s t → State s → State t
  execCode ε        st = st
  execCode (i ◅ is) st = execCode is (execInstr i st)
-}
