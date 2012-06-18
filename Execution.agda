module Execution where

open import Function
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.List
open import Data.Star
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded as WF

open import TypeUniverse
open import Expression
open import Denotation
open import Machine
open import Measure

-- Unwind the shape up to just below the top-most handler.
unwindShape : Shape → Maybe Shape
unwindShape (Han _ ∷ xs)  = just xs
unwindShape (Val _ ∷ xs)  = unwindShape xs
unwindShape []            = nothing

isJust : ∀ {a : Set} → Maybe a → Set
isJust (just _) = ⊤
isJust nothing  = ⊥

_$$_ : ∀ {a : Set} → (F : a → Set) → (x : Maybe a) → Set
F $$ just x = F x
F $$ nothing = ⊥

ij-lemma : ∀ {x st} → isJust (unwindShape (x :: st)) → isJust (unwindShape st)
ij-lemma {x} {st} tt = ?

unwindStack : ∀ {s} {ij : isJust (unwindShape s)} → Stack s → Stack $$ unwindShape s
unwindStack {[]} {()} snil
unwindStack (x :: st) = unwindStack {ij = tt} st
unwindStack (h !! st) = st

unwindCShape : ∀ {u s hs r} → (us : List U) → Code (s , u ∷ us ++ hs) (r , []) → Shape
unwindCShape us (PUSH x ◅ is) = unwindCShape us is
unwindCShape us (ADD    ◅ is) = unwindCShape us is
unwindCShape us (THROW  ◅ is) = unwindCShape us is
unwindCShape {u} us (MARK h ◅ is) = unwindCShape (u ∷ us) is
unwindCShape {u} (v ∷ us) (UNMARK ◅ is) = unwindCShape us is
unwindCShape {u} {Val .u ∷ Han .u ∷ s} {hs} [] (UNMARK ◅ is) = Val u ∷ s

unwindCode : ∀ {u s hs r} → (us : List U)
  → (is : Code (s , u ∷ us ++ hs) (r , []))
  → Code (unwindCShape us is , hs) (r , [])
unwindCode us (PUSH x ◅ is) = unwindCode us is
unwindCode us (ADD    ◅ is) = unwindCode us is
unwindCode us (THROW  ◅ is) = unwindCode us is
unwindCode us (MARK h ◅ is) = unwindCode (_ ∷ us) is
unwindCode (u ∷ us) (UNMARK ◅ is) = unwindCode us is
unwindCode [] (UNMARK ◅ is) = is

step : ∀ {s hs t ht r}
  → (i : Instr (s , hs) (t , ht))
  → (is : Code (t , ht) (r , []))
  → (st : Stack s)
  → State r
step (PUSH x) is            st  = ✓[ is ,   x   :: st ]
step  ADD     is (x :: y :: st) = ✓[ is , x + y :: st ]
step (MARK h) is            st  = ✓[ is ,   h   !! st ]
step  UNMARK  is (x :: h !! st) = ✓[ is ,   x   :: st ]
step {s} {hs = []     } THROW is st = ×[]
step {s} {hs = u ∷ hs'} THROW is st with unwindShape s
... | nothing = ×[]
... | just s' = ✓[ unwindCode [] is , {!!} ]

step-decr : ∀ {s hs t ht r}
  → (i : Instr (s , hs) (t , ht))
  → (is : Code (t , ht) (r , []))
  → (st : Stack s)
  → measureState (step i is st) < measureState ✓[ i ◅ is , st ]
step-decr i is st = {!!}

run' : ∀ {r} → (st : State r) → Acc _<'_ st → Result r
run' ×[] _ = Failure
run' ✓[ ε      , st ] _ = Success st
run' ✓[ i ◅ is , st ] (acc acc-st)
    = run' nextState (acc-st nextState next<current)
  where
    nextState = step i is st
    next<current = step-decr i is st



{-
-- Get the type of the top-most handler in the Shape.
unwindHnd : Shape → ℕ → Maybe U
unwindHnd (Han u ∷ xs) zero    = just u
unwindHnd (Han _ ∷ xs) (suc n) = unwindHnd xs n
unwindHnd (Val _ ∷ xs) n       = unwindHnd xs n
unwindHnd []           _       = nothing

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
