module Execution where

open import Function
open import Data.Nat
open import Data.Sum
open import Data.List
open import Data.Star
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import TypeUniverse
open import Expression
open import Denotation
open import Code

data _+ (a : Set) : Set where
  S   : a → a +
  _∷_ : a → a + → a +

unwindShape : Shape → U + → Shape
unwindShape (Han _ ∷ xs) (S _)    = xs
unwindShape (Han _ ∷ xs) (_ ∷ us) = unwindShape xs us
unwindShape (Val _ ∷ xs) us       = unwindShape xs us
unwindShape []           _        = []

data Resume (s : Shape) : Set where
  Succ : {u : U} → Code s (Val u ∷ s) → Stack s → Resume s
  Fail : Resume s

unwindStack : ∀ {s} → Stack s → (us : U +) → Resume (unwindShape s us)
unwindStack (h !! xs) (S _)    = Succ h xs
unwindStack (_ !! xs) (u ∷ us) = unwindStack xs us
unwindStack (_ :: xs) us       = unwindStack xs us
unwindStack snil      _        = Fail

data State (s : Shape) : Set where
  ✓[_] : Stack s → State s
  ![_,_] : (us : U +) → Resume (unwindShape s us) → State s

mutual
  -- Instruction execution
  execInstr : ∀ {s t} → Instr s t → State s → State t
  
  -- Normal operation
  execInstr ADD      ✓[ x :: y :: st ] = ✓[ (x + y) :: st ]
  execInstr UNMARK   ✓[ x :: _ !! st ] = ✓[       x :: st ]
  execInstr (PUSH x) ✓[           st ] = ✓[       x :: st ]
  execInstr (MARK h) ✓[           st ] = ✓[       h !! st ]

  -- Exception throwing
  execInstr (THROW {u}) ✓[ st ] = ![ S u , unwindStack st (S _) ]

  -- Non-trivial exception processing
  execInstr (UNMARK {v} {s})   ![ S u    , Succ h st ] = {! execCode h ✓[ st ] !}
  execInstr UNMARK   ![ S u    , Fail ]      = ![ S u , Fail ]
  execInstr UNMARK   ![ u ∷ us , r ]         = ![ us     , r ]
  execInstr (MARK {u} _) ![ us , r ]         = ![ u ∷ us , r ]
  
  -- Trivial exception processing: instruction skipping
  execInstr THROW    ![ n , r ] = ![ n , r ]
  execInstr ADD      ![ n , r ] = ![ n , r ]
  execInstr (PUSH _) ![ n , r ] = ![ n , r ]

  -- Code execution
  execCode : ∀ {s t} → Code s t → State s → State t
  execCode ε        st = st
  execCode (i ◅ is) st = execCode is (execInstr i st)


