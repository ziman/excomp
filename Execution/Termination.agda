module Execution.Termination where

open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.List
open import Data.Star
open import Data.Unit hiding (_≤_)
open import Data.Maybe
open import Data.Product

open import Algebra
open import Algebra.Structures
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import TypeUniverse
open import Expression
open import Denotation
open import Code
open import Execution.Informative
open import Execution.Utils
open import Execution.Forks

{-
postulate
  funext-dep : ∀ {a : Set} {b : a → Set} → (f g : (x : a) → b x) → (∀ x → f x ≡ g x) → f ≡ g

mutual
  irrInstr : ∀ {s t st} (i : Instr s t) (p q : AccInstr s t i st) → p ≡ q
  irrInstr ADD aiAdd aiAdd = refl
  irrInstr (PUSH x) aiPush aiPush = refl
  irrInstr THROW aiThrow aiThrow = refl
  irrInstr (MARK h) aiMark aiMark = refl
  irrInstr {Val u ∷ Han .u ∷ s} .{Val u ∷ s} { ✓[ st ] } UNMARK aiUnmark✓ aiUnmark✓ = refl
  irrInstr {Val u ∷ Han .u ∷ s} .{Val u ∷ s} { ![ suc n , r ] } UNMARK aiUnmark! aiUnmark! = refl
  irrInstr {Val u ∷ Han .u ∷ s} .{Val u ∷ s} { ![ zero , Okay h st ] } UNMARK (aiHandle p) (aiHandle q)
    = cong aiHandle (funext-dep p q (λ st → irrCode h (p st) (q st)))

  irrCode : ∀ {s t st} (c : Code s t) (p q : AccCode s t c st) → p ≡ q
  irrCode ε trivial trivial = refl
  irrCode (i ◅ is) (step ai p) (step aj q) rewrite irrInstr i ai aj
    = cong _ (irrCode is p q)

Acc : ∀ {s t} → Code s t → Set
Acc c = ∀ st → AccCode _ _ c st

acc-cons : ∀ {s t u} (st : State s) (i : Instr s t) (is : Code t u)
  → (ai : AccInstr s t i st)
  → AccCode s u (i ◅ is) st
  → AccCode t u is (execInstr i st ai)
acc-cons st i is ai (step aj ac) rewrite irrInstr i ai aj = ac

acc-app : ∀ {s t v u st} (c : Code s (Val v ∷ Han v ∷ t)) (d : Code (Val v ∷ t) u)
  → AccCode _ _ c st → (∀ st' → AccCode _ _ d st') → AccCode _ _ (c ◅◅ UNMARK ◅ d) st
acc-app {.(Val v ∷ Han v ∷ t)} {t} {v} {u} { ✓[ x :: h !! st ] } ε d ac ad 
  = step aiUnmark✓ (ad ✓[ x :: st ])
acc-app {.(Val v ∷ Han v ∷ t)} {t} {v} {u} { ![ suc n , r ] } ε d ac ad 
  = step aiUnmark! (ad ![ n , r ])
acc-app {Val v ∷ Han .v ∷ t} .{t} .{v} {u} { ![ zero , Okay .{v} h st ] } ε d ac ad
  = step (aiHandle λ st' → {!!} ) (ad _)
acc-app (PUSH x ◅ is) d (step aiPush  y) ad = step aiPush (acc-app is d y ad)
acc-app (ADD    ◅ is) d (step aiAdd   y) ad = step aiAdd (acc-app is d y ad)
acc-app (MARK h ◅ is) d (step aiMark  y) ad = step aiMark (acc-app is d y ad)
acc-app (THROW  ◅ is) d (step aiThrow y) ad = step aiThrow (acc-app is d y ad)
acc-app (UNMARK ◅ is) d (step aiUnmark✓ y) ad = step aiUnmark✓ (acc-app is d y ad)
acc-app (UNMARK ◅ is) d (step aiUnmark! y) ad = step aiUnmark! (acc-app is d y ad)
acc-app (UNMARK ◅ is) d (step (aiHandle hc) y) ad = step (aiHandle hc) (acc-app is d y ad)

term' : ∀ {s t} {c : Code s t} → Forks c → ∀ st → AccCode s t c st
term' Nil _ = trivial
term' (Push  f) st = step aiPush  (term' f _)
term' (Throw f) st = step aiThrow (term' f _)
term' (Add   f) st = step aiAdd   (term' f _)
term' (Branch {u} {s} {t} {r} {h} {is} rf hf isf) st
  = step aiMark (acc-app r is (term' rf _) (term' isf))

term : ∀ {s t} → (c : Code s t) → Closed c → ∀ st → AccCode s t c st
term c pf = term' (fork c pf)
-}

data Trace : ∀ {s t} → Code s t → State s → Set where
  tε : ∀ {s st} → Trace {s} {s} ε st 
  tPush✓ : ∀ {s t u} {st : Stack s} {is : Code (Val u ∷ s) t} x
    → Trace is ✓[ x :: st ] → Trace (PUSH x ◅ is) ✓[ st ]
  tPush! : ∀ {s t u n r} {is : Code (Val u ∷ s) t} x
    → Trace is ![ n , r ] → Trace (PUSH x ◅ is) ![ n , r ]
  tAdd✓ : ∀ {s t x y} {st : Stack s} {is : Code _ t}
    → Trace is ✓[ (x + y) :: st ] → Trace (ADD ◅ is) ✓[ x :: y :: st ]
  tAdd! : ∀ {s t n r} {is : Code (Val Nat ∷ s) t}
    → Trace is ![ n , r ] → Trace (ADD ◅ is) ![ n , r ]
  tThrow✓ : ∀ {s t u} {st : Stack s} {is : Code (Val u ∷ s) t}
    → Trace is ![ zero , unwindStack st zero ] → Trace (THROW ◅ is) ✓[ st ]
  tThrow! : ∀ {s t u n r} {is : Code (Val u ∷ s) t}
    → Trace is ![ n , r ] → Trace (THROW ◅ is) ![ n , r ]
  tMark✓ : ∀ {s t u h} {st : Stack s} {is : Code (Han u ∷ s) t}
    → Trace is ✓[ h !! st ] → Trace (MARK h ◅ is) ✓[ st ]
  tMark! : ∀ {s t u h n r} {is : Code (Han u ∷ s) t}
    → Trace is ![ suc n , r ] → Trace (MARK h ◅ is) ![ n , r ]
  tUnmark✓ : ∀ {s t u x h} {st : Stack s} {is : Code (Val u ∷ s) t}
    → Trace is ✓[ x :: st ] → Trace (UNMARK ◅ is) ✓[ x :: h !! st ]
  tUnmark! : ∀ {s t u n r} {is : Code (Val u ∷ s) t}
    → Trace is ![ n , r ] → Trace (UNMARK ◅ is) ![ suc n , r ]
  tHandle : ∀ {s t u h} {st : Stack s} {is : Code (Val u ∷ s) t}
    → (∀ st' → Trace h st')
    → (∀ st' → Trace is st')
    → Trace (UNMARK ◅ is) ![ zero , Okay h st ]

hnd : Shape → List (U × Shape)
hnd [] = []
hnd (Val u ∷ xs) = hnd xs
hnd (Han u ∷ xs) = (u , xs) ∷ hnd xs

data Handlers : List (U × Shape) → Set where
  hnil : Handlers []
  hcons : ∀ {u s xs}
    → (h : Code s (Val u ∷ s))
    → (∀ st → Trace h st)
    → Handlers xs
    → Handlers ((u , s) ∷ xs)

trace : ∀ {s t} → Handlers (hnd s) → (c : Code s t) → (st : State s) → Trace c st
trace hs ε st = tε
trace hs (PUSH x ◅ is) ✓[           st ] = tPush✓ x (trace hs is ✓[       x :: st ])
trace hs (ADD    ◅ is) ✓[ x :: y :: st ] = tAdd✓    (trace hs is ✓[ (x + y) :: st ])
trace hs (THROW  ◅ is) ✓[           st ] = tThrow✓  (trace hs is ![ zero , unwindStack st zero ])

trace hs (PUSH x ◅ is) ![ n , r ] = tPush! x (trace hs is ![ n , r ])
trace hs (ADD    ◅ is) ![ n , r ] = tAdd!    (trace hs is ![ n , r ])
trace hs (THROW  ◅ is) ![ n , r ] = tThrow!  (trace hs is ![ n , r ])

trace hs (MARK h ◅ is) ✓[ st ]    = tMark✓ (trace (hcons h (trace hs h) hs) is ✓[ h !! st ])
trace hs (MARK h ◅ is) ![ n , r ] = tMark! (trace (hcons h (trace hs h) hs) is ![ suc n , r ])

trace {Val u ∷ Han .u ∷ s} (hcons _ _ hs) (UNMARK ◅ is) ✓[ x :: _ !! st ] = tUnmark✓ (trace hs is ✓[ x :: st ])
trace {Val u ∷ Han .u ∷ s} (hcons _ _ hs) (UNMARK ◅ is) ![ suc n , r ] = tUnmark! (trace hs is ![ n , r ]) 
trace {Val u ∷ Han .u ∷ s} (hcons .h t' hs) (UNMARK ◅ is) ![ zero , Okay h st ]
  = tHandle {!!} (trace hs is)

{-
simh : ∀ {s t} → (c : Code s t) → Handlers (handlers s) → Handlers (handlers t)
simh ε hnd = hnd
simh (PUSH _ ◅ is) hnd = simh is hnd
simh (ADD    ◅ is) hnd = simh is hnd
simh (THROW  ◅ is) hnd = simh is hnd
simh (MARK h ◅ is) hnd = simh is (hcons h {!!} hnd)
simh (UNMARK ◅ is) (hcons h hc hnd) = simh is hnd
-}
{-
term : ∀ {s t} → (c : Code s t) → Handlers (hnd s) → ∀ st → AccCode _ _ c st
term ε hnd st = trivial
term (PUSH _ ◅ is) hnd st = step aiPush  (term is hnd _)
term (ADD    ◅ is) hnd st = step aiAdd   (term is hnd _)
term (THROW  ◅ is) hnd st = step aiThrow (term is hnd _)
term (MARK h ◅ is) hnd st = step aiMark  (term is (hcons h (λ st → term h hnd ✓[ st ]) hnd) _)
term (UNMARK ◅ is) (hcons h hc hnd) ✓[ st ] = step aiUnmark✓ (term is hnd _)
term (UNMARK ◅ is) (hcons h hc hnd) ![ suc n , r ] = step aiUnmark! (term is hnd _)
term (UNMARK ◅ is) (hcons h hc hnd) ![ zero , Okay h st ] = step (aiHandle {!!}) (term is hnd _)
-}
