module Execution.Termination where

open import Function
open import Data.Nat
open import Data.Sum
open import Data.List
open import Data.Star
open import Data.Unit
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

Invariant : ∀ {s t} → (c : Code' s t) → (st : State s) → Set
Invariant ε _ = ⊤
Invariant (ADD'      ◅ is) ✓[ x :: y :: st ] = Invariant is ✓[ (x + y) :: st ]
Invariant (UNMARK' h ◅ is) ✓[ x :: _ !! st ] = Invariant is ✓[ x :: st ]
Invariant (PUSH'   x ◅ is) ✓[ st ] = Invariant is ✓[ x :: st ]
Invariant (MARK'   h ◅ is) ✓[ st ] = Invariant is ✓[ h !! st ]
Invariant (THROW'    ◅ is) ✓[ st ] = Invariant is ![ zero , unwindStack st zero ]
Invariant (ADD'      ◅ is) ![ n , r ] = Invariant is ![ n , r ]
Invariant (PUSH'   _ ◅ is) ![ n , r ] = Invariant is ![ n , r ]
Invariant (THROW'    ◅ is) ![ n , r ] = Invariant is ![ n , r ]
Invariant (MARK'   h ◅ is) ![ n , r ] = Invariant is ![ suc n , r ]
Invariant (UNMARK' _ ◅ is) ![ suc n , r ] = Invariant is ![ n , r ]
Invariant (UNMARK' h ◅ is) ![ zero , Okay g st ]
  = ∃ λ ac → (revert h ≡ g) × (Invariant h ✓[ st ]) × (Invariant is (execCode (revert h) ✓[ st ] ac))

acc : ∀ {s t} → (c : Code' s t) → (st : State s) → Invariant c st → AccCode s t (revert c) st
acc ε _ _ = trivial
acc (ADD'      ◅ is) ✓[ x :: y :: st ] inv = step aiAdd     (acc is ✓[ (x + y) :: st ] inv)
acc (UNMARK' h ◅ is) ✓[ x :: _ !! st ] inv = step aiUnmark✓ (acc is ✓[ x :: st ] inv)
acc (PUSH'   x ◅ is) ✓[           st ] inv = step aiPush    (acc is ✓[ x :: st ] inv)
acc (MARK'   h ◅ is) ✓[           st ] inv = step aiMark    (acc is ✓[ h !! st ] inv)
acc (ADD'      ◅ is) ![ n     , r    ] inv = step aiAdd     (acc is ![ n , r ] inv)
acc (PUSH'   x ◅ is) ![ n     , r    ] inv = step aiPush    (acc is ![ n , r ] inv)
acc (THROW'    ◅ is) ![ n     , r    ] inv = step aiThrow   (acc is ![ n , r ] inv)
acc (MARK'   h ◅ is) ![ n     , r    ] inv = step aiMark    (acc is ![ suc n , r ] inv)
acc (UNMARK' h ◅ is) ![ suc n , r    ] inv = step aiUnmark! (acc is ![ n , r ] inv)
acc (THROW'    ◅ is) ✓[           st ] inv = step aiThrow   (acc is ![ zero , unwindStack st zero ] inv)
acc (UNMARK' h ◅ is) ![ zero  , Okay h' st ] (ac , rh=g , invh , invis) rewrite rh=g
    = step (aiHandle ac) (acc is (execCode h' ✓[ st ] ac) invis)

inv : ∀ {s t} → (c : Code' s t) → (st : State s) → Invariant c st
inv ε        st = tt
inv (ADD'      ◅ is) ✓[ x :: y :: st ] = inv is ✓[ (x + y) :: st ]
inv (ADD'      ◅ is) ![ n , r ] = inv is ![ n , r ]
inv (PUSH'   x ◅ is) ✓[ st ] = inv is ✓[ x :: st ]
inv (PUSH'   x ◅ is) ![ n , r ] = inv is ![ n , r ]
inv (THROW'    ◅ is) ✓[ st ] = inv is ![ zero , unwindStack st zero ]
inv (THROW'    ◅ is) ![ n , r ] = inv is ![ n , r ]
inv (MARK'   h ◅ is) ✓[ st ] = inv is ✓[ h !! st ]
inv (MARK'   h ◅ is) ![ n , r ] = inv is ![ suc n , r ]
inv (UNMARK' h ◅ is) ✓[ x :: g !! st ] = inv is ✓[ x :: st ]
inv (UNMARK' h ◅ is) ![ suc n , r ] = inv is ![ n , r ]
inv (UNMARK' h ◅ is) ![ zero , Okay g st ] = acc h ✓[ st ] (inv h ✓[ st ]) , {!!} , {!!} , {!!}

