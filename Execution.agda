module Execution where

open import Function
open import Data.Nat
open import Data.Sum
open import Data.List

open import TypeUniverse
open import Expression
open import Denotation
open import Code
open import Compiler

unwind : Shape → Shape
unwind [] = []
unwind (Val _ ∷ xs) = unwind xs
unwind (Han u ∷ xs) = Val u ∷ xs

_>>=_ : ∀ {s t w} → (Stack s ⊎ Stack w) → (Stack s → Stack t ⊎ Stack t) → Stack [] ⊎ Stack t
_>>=_ (inj₁ snil) _ = inj₁ snil 
_>>=_ (inj₂ st)   f = f st

execInstr : ∀ {s t} → Instr s t → Stack s → Stack t ⊎ Stack (unwind t)
execInstr _ st = inj₁ snil

-- Execute a code block above the given stack.
exec : ∀ {s t} → Code s t → Stack s → Stack t ⊎ Stack (unwind t)
exec cnil      st = inj₁ st
exec (i ,, is) st = execInstr i st >>= exec is
{-
exec cnil            st             = st
exec (PUSH x ,, is)  st             = exec is (x :: st)
exec (THROW  ,, is)  st             = exec is (■:: st)
exec (MARK h ,, is)  st             = exec is (h !! st)
exec (UNMARK ,, is)  (v :: _ !! st) = exec is (v :: st) 
exec (UNMARK ,, is)  (■::(h !! st)) = exec is (exec h st)
exec (ADD    ,, is)  (x :: y :: st) = exec is ((x + y) :: st)
exec (ADD    ,, is)  (■::(_ :: st)) = exec is (■:: st)
exec (ADD    ,, is)  (_ ::  ■:: st) = exec is (■:: st)
exec (ADD    ,, is)  (■:: (■:: st)) = exec is (■:: st)
-}
