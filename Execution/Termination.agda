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
  accInstr : ∀ {s t} i st → AccInstr s t i st
  accInstr ADD      _ = aiAdd
  accInstr (PUSH _) _ = aiPush
  accInstr THROW    _ = aiThrow
  accInstr (MARK _) _ = aiMark
  accInstr UNMARK ✓[ st ] = aiUnmark✓
  accInstr UNMARK ![ suc n , r ] = aiUnmark!
  accInstr UNMARK ![ zero  , Okay h st ] = aiHandle (accCode h ✓[ st ])

  accCode : ∀ {s t} c st → AccCode s t c st
  accCode ε        _  = trivial
  accCode (i ◅ is) st = step ai ac
    where
      ai = accInstr i st
      ac = accCode is (execInstr i st ai)
