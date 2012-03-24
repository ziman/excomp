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
  execInstr : ∀ {s t} → (i : Instr s t) → State s → State t
  
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
  execCode : ∀ {s t} → (c : Code s t) → State s → State t
  execCode ε        st = st
  execCode (i ◅ is) st = execCode is (execInstr i st)

data Handler : Shape → Shape → Set where
  Cong : ∀ {s t u}
    → Handler s t
    → Handler (Val u ∷ s) t
  Push : ∀ {s t u}
    → Code s (Val u ∷ s)
    → Handler s t
    → Handler (Han u ∷ s) t
  Unhandled : ∀ {s t} → Handler s t

HShape : Set
HShape = List (Shape × Shape)

step : ∀ {s t u} → Instr s t → Handler s u → Handler t u
step (MARK h') h                  = Push h' h
step _         Unhandled          = Unhandled
step ADD       (Cong (Cong h))    = Cong h
step ADD       (Cong Unhandled)   = Unhandled
step (PUSH _)  h                  = Cong h
step THROW     h                  = Cong h
step UNMARK    (Cong (Push h' h)) = Cong h
step UNMARK    (Cong Unhandled)   = Unhandled

data Term : ∀ {s t} → Code s t → Set where
  Now : ∀ {s} → Term {s} {s} ε
  Later : ∀ {s t u} {i : Instr s t} {c : Code t u} → Term c → Term (i ◅ c)

data _×'_ {a b : Set} (P Q : a → b → Set) : a → b → Set where
  _,'_ : ∀ {x y} → P x y → Q x y → (P ×' Q) x y

Handler' : Shape → Shape → Shape → Set
Handler' t p q = Handler p t

annotate : ∀ {s t} → Star Instr s t → Star (Instr ×' Handler' t) s t
annotate c = annotate' c Unhandled
  where
    annotate' : ∀ {s u} → Star Instr s u → Handler s u → Star (Instr ×' Handler' u) s u
    annotate' ε        h = ε
    annotate' (i ◅ is) h = (i ,' h) ◅ annotate' is (step i h)

