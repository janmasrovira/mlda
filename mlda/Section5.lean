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

namespace CA

variable
  {P V : Type}
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  [Fintype V]
  [DecidableEq V]

inductive Val where
  | zero
  | half
  | one
  deriving DecidableEq, FinEnum

instance : OfNat Val 0 where
  ofNat := .zero

instance : OfNat Val 1 where
  ofNat := .one

scoped notation " ½ " => Val.half

inductive Sig where
  | input
  | echo₁
  | echo₂
  | output

export Sig (input echo₁ echo₂ output)

class Thy (μ : Model Sig P Val) where
  CaEcho1? : ⊨[μ] ∀ₑ ([echo₁]ₑ ⇀ₑ ◇ₑ [input]ₑ)
  CaEcho2? : ⊨[μ] ∀ₑ ([echo₂]ₑ ⇀ₑ ⊡ₑ [echo₁]ₑ)
  CaOutput? : ⊨[μ] ([output, .val 0]ₑ →ₑ ⊡ₑ [echo₂, .val 0]ₑ) ∧ₑ
                     ([output, .val 1]ₑ →ₑ ⊡ₑ [echo₂, .val 1]ₑ)
  CaOutput'? : ⊨[μ] [output, .val ½]ₑ →ₑ (⊡ₑ [echo₁, .val 0]ₑ ∧ₑ ⊡ₑ [echo₁, .val 1]ₑ)
  CaCorrectInput {s : Sig} : ⊨[μ] ⊡ₑ TF[s]ₑ
  CaCorrect' {s : Sig} := ⊨[μ] TF[s]ₑ ∨ₑ B[s]ₑ
  CaInput : ⊨[μ] ([input, .val 0]ₑ ⊕ₑ [input, .val 1]ₑ) ∧ₑ (¬ₑ [input, .val ½]ₑ)
  CaEcho2Affine : ⊨[μ] ∃₀₁ₑ [echo₂]ₑ
  CaEcho1! : ⊨[μ] ∀ₑ (([input]ₑ ∨ₑ ⟐ₑ [echo₁]ₑ) →ₑ [echo₁]ₑ)
  CaEcho2! : ⊨[μ] (∃⁎ₑ (⊡ₑ [echo₁]ₑ)) →ₑ ∃⁎ₑ [echo₂]ₑ
  CaOutput! : ⊨[μ] ∀ₑ (⊡ₑ [echo₂]ₑ →ₑ [output]ₑ)
  CaOutput'! : ⊨[μ] (⊡ₑ [echo₁, .val 0]ₑ ∧ₑ ⊡ₑ [echo₁, .val 1]ₑ) →ₑ [output, .val ½]ₑ

end CA
