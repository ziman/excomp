module Execution where

open import Function
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.List
open import Data.Star
open import Data.Maybe
open import Data.Product

open import Algebra.Structures
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import TypeUniverse
open import Expression
open import Denotation
open import Code

-- Get the type of the top-most handler in the Shape.
unwindHnd : Shape → ℕ → Maybe U
unwindHnd (Han u ∷ xs) zero    = just u
unwindHnd (Han _ ∷ xs) (suc n) = unwindHnd xs n
unwindHnd (Val _ ∷ xs) n       = unwindHnd xs n
unwindHnd []           _       = nothing

-- Unwind the shape up to just below the top-most handler.
unwindShape : Shape → ℕ → Shape
unwindShape (Han _ ∷ xs) zero    = xs
unwindShape (Han _ ∷ xs) (suc n) = unwindShape xs n
unwindShape (Val _ ∷ xs) n       = unwindShape xs n
unwindShape []           _       = []

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
  measureInstr : ∀ {s t} → Instr s t → ℕ
  measureInstr (PUSH x) = 1
  measureInstr  ADD     = 1
  measureInstr (MARK x) = 1 + measureCode x
  measureInstr  UNMARK  = 1
  measureInstr  THROW   = 1

  measureCode : ∀ {s t} → Code s t → ℕ
  measureCode ε        = 0
  measureCode (i ◅ is) = 1 + measureInstr i + measureCode is

  measureState : ∀ {s} → State s → ℕ
  measureState ✓[ st ] = measureStack st
  measureState {s} ![ n , y ] with unwindHnd s n
  measureState {s} ![ n , Okay h st ] | just u  = measureCode h + measureStack st
  measureState {s} ![ n , Fail      ] | nothing = 0

  measureStack : ∀ {s} → Stack s → ℕ
  measureStack snil      = 0
  measureStack (_ :: xs) = measureStack xs
  measureStack (h !! xs) = measureCode h + measureStack xs

suc=suc : ∀ {x y} → suc x ≡ suc y → x ≡ y
suc=suc {x} .{x} refl = refl

≥-≠ : ∀ {m n} → m ≥ n → ¬ (m ≡ n) → m ≥ suc n
≥-≠ {zero}  z≤n m≠n = ⊥-elim (m≠n refl)
≥-≠ {suc m} z≤n m≠n = s≤s z≤n
≥-≠ {suc m} {suc n} (s≤s p) m≠n = s≤s (≥-≠ p (m≠n ∘ cong suc))

≤-≠ : ∀ {m n} → m ≤ suc n → ¬ (suc n ≡ m) → m ≤ n
≤-≠ z≤n       sm≠n = z≤n
≤-≠ (s≤s m≤n) sm≠n = ≥-≠ m≤n (sm≠n ∘ cong suc)

≤-zero : ∀ {n} → n ≤ zero → zero ≡ n
≤-zero {zero } pf = refl
≤-zero {suc n} ()

≤-refl : ∀ {m n} → m ≡ n → m ≤ n
≤-refl {zero}  .{zero}  refl = z≤n
≤-refl {suc n} .{suc n} refl = s≤s (≤-refl refl)

m+n+k=m+k+n : ∀ {m n k} → m + n + k ≡ m + k + n
m+n+k=m+k+n {m} {n} {k} = begin
    m + n + k
      ≡⟨ +-assoc m n k ⟩
    m + (n + k)
      ≡⟨ cong (λ x → m + x) (+-comm n k) ⟩
    m + (k + n)
      ≡⟨ sym (+-assoc m k n) ⟩
    m + k + n
      ∎
  where
    open ≡-Reasoning
    open IsCommutativeSemiring Data.Nat.Properties.isCommutativeSemiring using (+-isCommutativeMonoid)
    open IsCommutativeMonoid +-isCommutativeMonoid using () renaming (assoc to +-assoc; comm to +-comm)

mutual
  -- Instruction execution
  execInstr : ∀ {s t}
    → (i : Instr s t) → (st : State s)
    → (m : ℕ) → m ≡ measureInstr i + measureState st
    → State t
  
  -- Normal operation
  execInstr ADD      ✓[ x :: y :: st ] _ _ = ✓[ (x + y) :: st ]
  execInstr UNMARK   ✓[ x :: _ !! st ] _ _ = ✓[       x :: st ]
  execInstr (PUSH x) ✓[           st ] _ _ = ✓[       x :: st ]
  execInstr (MARK h) ✓[           st ] _ _ = ✓[       h !! st ]

  -- Exception throwing
  -- Unwind the stack, creating a resumption point. Instruction skipping begins.
  execInstr THROW ✓[ st ] _ _ = ![ zero , unwindStack st zero  ]

  -- Non-trivial exception processing
  execInstr (MARK _) ![ n     , r         ] _ _ = ![ suc n , r ]
  execInstr UNMARK   ![ suc n , r         ] _ _ = ![ n     , r ]

  -- Exception handling
  execInstr UNMARK ![ zero , Okay h st ] zero    ()
  execInstr UNMARK ![ zero , Okay h st ] (suc m) pf = execCode h ✓[ st ] m (suc=suc pf)

  -- Trivial exception processing: instruction skipping
  execInstr THROW    ![ n , r ] _ _ = ![ n , r ]
  execInstr ADD      ![ n , r ] _ _ = ![ n , r ]
  execInstr (PUSH _) ![ n , r ] _ _ = ![ n , r ]

  execInstr' : ∀ {s t}
    → (i : Instr s t) → (st : State s)
    → (m : ℕ) → m ≥ measureInstr i + measureState st
    → State t
  execInstr' i st m pf with m ≟ measureInstr i + measureState st
  execInstr' i st m       pf | yes p = execInstr i st m p
  execInstr' i st zero    pf | no  p with p (≤-zero pf)
  ... | ()
  execInstr' i st (suc m) pf | no  p = execInstr' i st m (≤-≠ pf p)

  execCode' : ∀ {s t}
    → (c : Code s t) → (st : State s)
    → (m : ℕ) → m ≥ measureCode c + measureState st
    → State t
  execCode' c st m pf with m ≟ measureCode c + measureState st
  execCode' c st m       pf | yes p = execCode c st m p
  execCode' c st zero    pf | no  p with p (≤-zero pf)
  ... | ()
  execCode' c st (suc m) pf | no  p = execCode' c st m (≤-≠ pf p)

  -- Code execution
  -- This is a left fold over instructions.
  execCode : ∀ {s t}
    → (c : Code s t) → (st : State s)
    → (m : ℕ) → m ≡ measureCode c + measureState st
    → State t
  execCode ε        st _ _  = st
  execCode (i ◅ is) st zero    ()
  execCode (i ◅ is) st (suc m) pf = execCode' is st' m (codeCode i is st m pf' pf)
    where
      pf' = codeInstr i is st m pf
      st' = execInstr' i st m pf'

  codeInstr : ∀ {s t u} (i : Instr s t) (is : Code t u) (st : State s) (m : ℕ)
    → suc m ≡ measureCode (i ◅ is) + measureState st
    → m ≥ measureInstr i + measureState st
  codeInstr i is st m pf with ≤-refl (sym pf)
  ... | s≤s le = begin
      measureInstr i + measureState st
        ≤⟨ m≤m+n _ _ ⟩
      measureInstr i + measureState st + measureCode is      
        ≡⟨ m+n+k=m+k+n {measureInstr i} {measureState st} {measureCode is} ⟩
      measureInstr i + measureCode is + measureState st
        ≤⟨ le ⟩
      m ∎
    where
      open ≤-Reasoning

  ≤-suc : ∀ {x} → x ≤ suc x
  ≤-suc = ≤-step (≤-refl refl)

  codeLemma : ∀ {s t u} (i : Instr s t) (is : Code t u) (st : State s) (m : ℕ) (pf : m ≥ measureInstr i + measureState st)
    → measureState (execInstr' i st m pf) ≤ measureInstr i + measureState st
  codeLemma (PUSH y) is st m pf with m ≟ suc (measureState st)
  codeLemma (PUSH y) is ✓[ st    ] m pf | yes  p = ≤-suc
  codeLemma {s} (PUSH y) is ![ n , r ] m pf | yes p with unwindHnd s n 
  ... | just u  = ≤-step (≤-refl {!refl!})
  ... | nothing = {!!}
  codeLemma (PUSH y) is ✓[ st    ] m pf | no  ¬p = {!!}
  codeLemma (PUSH y) is ![ n , r ] m pf | no  ¬p = {!!}
  codeLemma  ADD     is st m pf = {!!}
  codeLemma (MARK y) is st m pf = {!!}
  codeLemma  UNMARK  is st m pf = {!!}
  codeLemma  THROW   is st m pf = {!!}

  codeCode : ∀ {s t u} (i : Instr s t) (is : Code t u) (st : State s) (m : ℕ) (pf : m ≥ measureInstr i + measureState st)
    → suc m ≡ measureCode (i ◅ is) + measureState st
    → m ≥ measureCode is + measureState (execInstr' i st m pf)
  codeCode i is st m pf geq with ≤-refl (sym geq)
  ... | s≤s le = begin
      measureCode is + measureState (execInstr' i st m pf)
        ≤⟨ {!!} ⟩
      measureCode is + (measureInstr i + measureState st)
        ≡⟨ +-comm (measureCode is) _ ⟩
      measureInstr i + measureState st + measureCode is
        ≡⟨ m+n+k=m+k+n {measureInstr i} {measureState st} {measureCode is} ⟩
      measureInstr i + measureCode is + measureState st
        ≤⟨ le ⟩
      m ∎
    where
      open ≤-Reasoning
      open IsCommutativeSemiring Data.Nat.Properties.isCommutativeSemiring using (+-isCommutativeMonoid)
      open IsCommutativeMonoid +-isCommutativeMonoid using () renaming (assoc to +-assoc; comm to +-comm)

