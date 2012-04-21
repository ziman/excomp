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
open import Execution.Forks

mutual
  data State (s : Shape) : Set where
    ✓[_] : Stack s → State s
    ![_,_] : (n : ℕ) → Resume (unwindShape s n) (unwindHnd s n) → State s

  infixr 50 _::_
  infixr 50 _!!_
  data Stack : Shape → Set where
    snil : Stack []
    _::_ : ∀ {u s} → el u → Stack s → Stack (Val u ∷ s)
    _!!_ : ∀ {u s} → (∃ λ (c : Code s (Val u ∷ s)) → Closed c) → Stack s → Stack (Han u ∷ s)

  data Resume (s : Shape) : Maybe U → Set where
    Okay : ∀ {u} → (∃ λ (c : Code s (Val u ∷ s)) → Closed c) → (st : Stack s) → Resume s (just u)
    Fail : Resume s nothing

  unwindStack : ∀ {s} → Stack s → (n : ℕ) → Resume (unwindShape s n) (unwindHnd s n)
  unwindStack (h !! xs) zero    = Okay h xs
  unwindStack (_ !! xs) (suc n) = unwindStack xs n
  unwindStack (_ :: xs) n       = unwindStack xs n
  unwindStack snil      _       = Fail

  -- Accessibility of code (+ state)
  data Acc : ∀ {s t} → Code s t → Set where
    trivial : ∀ {s} → Acc {s} {s} ε
    step : ∀ {s t u} {i : Instr s t} {is : Code t u}
      → Acc is
      → Acc (i ◅ is)

  acc : ∀ {s t} (c : Code s t) → Acc c
  acc ε = trivial
  acc (_ ◅ is) = step (acc is)

  -- Instruction execution
  execInstr : ∀ {s t} → (i : Instr s t) → (st : State s) → State t

  -- Normal operation
  execInstr ADD        ✓[ x :: y :: st ] = ✓[ (x + y) :: st ]
  execInstr UNMARK     ✓[ x :: _ !! st ] = ✓[       x :: st ]
  execInstr (PUSH x)   ✓[           st ] = ✓[       x :: st ]
  execInstr (MARK h hc) ✓[           st ] = ✓[ (h , hc) !! st ]

  -- Exception throwing
  execInstr THROW ✓[ st ] = ![ zero , unwindStack st zero  ]

  -- Non-trivial exception processing
  execInstr (MARK _ _) ![ n     , r         ] = ![ suc n , r ]
  execInstr UNMARK   ![ suc n , r         ] = ![ n     , r ]
  execInstr UNMARK   ![ zero  , Okay (h , hc) st ] = exec h ✓[ st ] hc

  -- Trivial exception processing: instruction skipping
  execInstr THROW    ![ n , r ] = ![ n , r ]
  execInstr ADD      ![ n , r ] = ![ n , r ]
  execInstr (PUSH _) ![ n , r ] = ![ n , r ]

  -- Code execution
  exec : ∀ {s t n} → (c : Code s t) → (st : State s) → Balanced n c → State t
  exec ε        st bal-ε   = st
  exec (i ◅ is) st (step ac) = exec is (execInstr i st) ac

