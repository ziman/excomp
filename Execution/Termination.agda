module Execution.Termination where

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
open import Execution.Informative

mutual
  data Instr' : Shape → Shape → Set where
    ADD' : ∀ {s} → Instr' (Val Nat ∷ Val Nat ∷ s) (Val Nat ∷ s)
    PUSH' : ∀ {s u} → el u → Instr' s (Val u ∷ s)
    THROW' : ∀ {s u} → Instr' s (Val u ∷ s)
    MARK'  : ∀ {s u} → Code s (Val u ∷ s) → Instr' s (Han u ∷ s)
    UNMARK' : ∀ {s u} → Code' s (Val u ∷ s) → Instr' (Val u ∷ Han u ∷ s) (Val u ∷ s)

  Code' : Shape → Shape → Set
  Code' = Star Instr'

data HndStack : List (U × Shape) → Set where
  []' : HndStack []
  _∷'_ : ∀ {u s sh} → Code' s (Val u ∷ s) → HndStack sh → HndStack ((u , s) ∷ sh)

handlers : Shape → List (U × Shape)
handlers []          = []
handlers (Val _ ∷ s) = handlers s
handlers (Han u ∷ s) = (u , s) ∷ handlers s

shift : ∀ {s t} → Code s t → HndStack (handlers s) → Code' s t
shift ε             st = ε
shift (PUSH x ◅ is) st = PUSH' x ◅ shift is st
shift (ADD    ◅ is) st = ADD'    ◅ shift is st
shift (THROW  ◅ is) st = THROW'  ◅ shift is st
shift (MARK h ◅ is) st = MARK' h ◅ shift is (shift h st ∷' st)
shift (UNMARK ◅ is) (h ∷' st) = UNMARK' h ◅ shift is st

revert : ∀ {s t} → Code' s t → Code s t
revert ε = ε
revert (ADD'    ◅ is) = ADD    ◅ revert is
revert (PUSH' x ◅ is) = PUSH x ◅ revert is
revert (THROW'  ◅ is) = THROW  ◅ revert is
revert (MARK' h ◅ is) = MARK h ◅ revert is
revert (UNMARK' _ ◅ is) = UNMARK ◅ revert is

shift-revert-inv : ∀ {s t} (c : Code s t) (st : HndStack (handlers s)) → revert (shift c st) ≡ c
shift-revert-inv ε        st = refl
shift-revert-inv (PUSH x ◅ is) st = cong (_◅_ (PUSH x)) (shift-revert-inv is st)
shift-revert-inv (ADD    ◅ is) st = cong (_◅_ ADD)      (shift-revert-inv is st)
shift-revert-inv (THROW  ◅ is) st = cong (_◅_ THROW)    (shift-revert-inv is st)
shift-revert-inv (MARK h ◅ is) st = cong (_◅_ (MARK h)) (shift-revert-inv is (shift h st ∷' st))
shift-revert-inv (UNMARK ◅ is) (h ∷' st) = cong (_◅_ UNMARK) (shift-revert-inv is st)

data Invariant : ∀ {s t} → Code' s t → State s → Set where
  iAdd✓ : ∀ {s t is x y st}
    → Invariant {Val Nat ∷ s} {t} is ✓[ (x + y) :: st ]
    → Invariant (ADD' ◅ is) ✓[ x :: y :: st ]
  iUnmark✓ : ∀ x h st is
    → Invariant is ✓[ x :: st ]
    → Invariant (UNMARK' h ◅ is) ✓[ x :: (revert h) !! st ]
  iPush✓ : ∀ {x is st}
    → Invariant is ✓[ x :: st ]
    → Invariant (PUSH' x ◅ is) ✓[ st ]
  iMark✓ : ∀ {h is st}
    → Invariant is ✓[ h !! st ]
    → Invariant (MARK' h ◅ is) ✓[ st ]
  iAdd! : ∀ {is n r}
    → Invariant is ![ n , r ]
    → Invariant (ADD' ◅ is) ![ n , r ]
  iPush! : ∀ {is x n r}
    → Invariant is ![ n , r ]
    → Invariant (PUSH' x ◅ is) ![ n , r ]
  iThrow! : ∀ {is n r}
    → Invariant is ![ n , r ]
    → Invariant (THROW' ◅ is) ![ n , r ]
  iMark! : ∀ {h is n r}
    → Invariant is ![ suc n , r ]
    → Invariant (MARK' h ◅ is) ![ n , r ]
  iUnmark! : ∀ {h is n r}
    → Invariant is ![ n , r ]
    → Invariant (UNMARK' h ◅ is) ![ suc n , r ]
  iThrow✓ : ∀ {is st}
    → Invariant is ![ zero , unwindStack st zero ]
    → Invariant (THROW' ◅ is) ✓[ st ]
  iHandle : ∀ {h is st ac}
    → Invariant is (execCode (revert h) ✓[ st ] ac)
    → Invariant is ✓[ st ]
    → Invariant (UNMARK' h ◅ is) ![ zero , Okay (revert h) st ]

acc : ∀ {s t} → (c : Code' s t) → (st : State s) → Invariant c st → AccCode s t (revert c) st
acc ε _ _ = trivial
acc (ADD'      ◅ is) ✓[ x :: y :: st ] (iAdd✓    i) = step aiAdd     (acc is ✓[ (x + y) :: st ] i)
acc .(UNMARK' h ◅ is) ✓[ .x :: .(revert h) !! .st ] (iUnmark✓ x h st is i) = step aiUnmark✓ (acc is ✓[ x :: st ] i)
acc (PUSH'   x ◅ is) ✓[           st ] (iPush✓   i) = step aiPush    (acc is ✓[ x :: st ] i)
acc (MARK'   h ◅ is) ✓[           st ] (iMark✓   i) = step aiMark    (acc is ✓[ h !! st ] i)
acc (ADD'      ◅ is) ![ n     , r    ] (iAdd!    i) = step aiAdd     (acc is ![ n , r ] i)
acc (PUSH'   x ◅ is) ![ n     , r    ] (iPush!   i) = step aiPush    (acc is ![ n , r ] i)
acc (THROW'    ◅ is) ![ n     , r    ] (iThrow!  i) = step aiThrow   (acc is ![ n , r ] i)
acc (MARK'   h ◅ is) ![ n     , r    ] (iMark!   i) = step aiMark    (acc is ![ suc n , r ] i)
acc (UNMARK' h ◅ is) ![ suc n , r    ] (iUnmark! i) = step aiUnmark! (acc is ![ n , r ] i)
acc (THROW'    ◅ is) ✓[           st ] (iThrow✓  i) = step aiThrow   (acc is ![ zero , unwindStack st zero ] i)
acc (UNMARK' h ◅ is) ![ zero  , Okay h' st ] (iHandle i j) = step {!!} {!!}

