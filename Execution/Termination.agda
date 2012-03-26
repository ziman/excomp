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

acc : ∀ {s t} → (c : Code' s t) → ∀ st → AccCode s t (revert c) st
acc ε _ = trivial
acc (ADD'      ◅ is) ✓[ x :: y :: st ] = step aiAdd     (acc is ✓[ (x + y) :: st ])
acc (UNMARK' _ ◅ is) ✓[ x :: _ !! st ] = step aiUnmark✓ (acc is ✓[ x :: st ])
acc (PUSH'   x ◅ is) ✓[           st ] = step aiPush    (acc is ✓[ x :: st ])
acc (MARK'   h ◅ is) ✓[           st ] = step aiMark    (acc is ✓[ h !! st ])
acc (ADD'      ◅ is) ![ n     , r    ] = step aiAdd     (acc is ![ n , r ])
acc (PUSH'   x ◅ is) ![ n     , r    ] = step aiPush    (acc is ![ n , r ])
acc (THROW'    ◅ is) ![ n     , r    ] = step aiThrow   (acc is ![ n , r ])
acc (MARK'   h ◅ is) ![ n     , r    ] = step aiMark    (acc is ![ suc n , r ])
acc (UNMARK' h ◅ is) ![ suc n , r    ] = step aiUnmark! (acc is ![ n , r ])
acc (THROW'    ◅ is) ✓[           st ] = step aiThrow   (acc is ![ zero , unwindStack st zero ])
acc (UNMARK' h ◅ is) ![ zero  , Okay h' st ] = step {!!} {!!}

