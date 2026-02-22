import mlda.Base
import mlda.Three
import mlda.FinSemitopology
import Mathlib.Tactic.Attr.Register
import mlda.Section3

open Three
open scoped Three.Atom
open scoped Three.Function
open scoped FinSemitopology
open FinSemitopology
open scoped Definitions
open Definitions
open scoped Notation
open Notation
open scoped Denotation
open Denotation

section

variable
  {P V : Type}
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  [Fintype V]
  [DecidableEq V]

inductive CASig where
  | input
  | echo₁
  | echo₂
  | output

export CASig (input echo₁ echo₂ output)

class ThyCA (μ : Model CASig P V) where
  CaEcho1? : ⊨[μ] ∀ₑ ([echo₁]ₑ ⇀ₑ ◇ₑ [input]ₑ)
  CaEcho2? : ⊨[μ] ∀ₑ ([echo₂]ₑ ⇀ₑ ⊡ₑ [echo₁]ₑ)
