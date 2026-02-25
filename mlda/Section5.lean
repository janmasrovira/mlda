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

class inductive NotHalf : Val → Prop
  | zero : NotHalf 0
  | one : NotHalf 1

instance : NotHalf 0 := .zero
instance : NotHalf 1 := .one

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
  CaCorrect (s : Sig) : ⊨[μ] ⊡ₑ TF[s]ₑ
  CaCorrect' {s : Sig} := ⊨[μ] TF[s]ₑ ∨ₑ B[s]ₑ
  CaInput : ⊨[μ] ([input, .val 0]ₑ ⊕ₑ [input, .val 1]ₑ) ∧ₑ (¬ₑ [input, .val ½]ₑ)
  CaEcho2Affine : ⊨[μ] ∃₀₁ₑ [echo₂]ₑ
  CaEcho1! : ⊨[μ] ∀ₑ (([input]ₑ ∨ₑ ⟐ₑ [echo₁]ₑ) →ₑ [echo₁]ₑ)
  CaEcho2! : ⊨[μ] (∃⁎ₑ (⊡ₑ [echo₁]ₑ)) →ₑ ∃⁎ₑ [echo₂]ₑ
  CaOutput! : ⊨[μ] ∀ₑ (⊡ₑ [echo₂]ₑ →ₑ [output]ₑ)
  CaOutput'! : ⊨[μ] (⊡ₑ [echo₁, .val 0]ₑ ∧ₑ ⊡ₑ [echo₁, .val 1]ₑ) →ₑ [output, .val ½]ₑ

namespace Thy

variable
  (μ : Model Sig P Val)
  [ca : Thy μ]
  {p : P}
  {v v' : Val}

theorem CaOutput?_simp [n : NotHalf v] : μ.ς output p v = .true → ⊨[μ] ⊡ₑ [echo₂, .val v]ₑ := by
  cases n
  · intro h;
    have c1 := ca.CaOutput?; specialize c1 p; rw [Lemmas.valid_and] at c1; obtain ⟨c0, c1⟩ := c1
    rw [Lemmas.valid_impl] at c0 c1; apply quorum_global'.mp; apply c0; simp [denotation]; exact h
  · intro h;
    have c1 := ca.CaOutput?; specialize c1 p; rw [Lemmas.valid_and] at c1; obtain ⟨c0, c1⟩ := c1
    rw [Lemmas.valid_impl] at c0 c1; apply quorum_global'.mp; apply c1; simp [denotation]; exact h

end Thy

namespace Proposition_5_3_3

variable
  (μ : Model Sig P Val)
  [ca : Thy μ]
  [twined : Twined3 μ.S]
  {v v' : Val}
  [NotHalf v] [NotHalf v']

theorem t : ⊨[μ] ((◇ₑ [output, .val v]ₑ ∧ₑ ◇ₑ [output, .val v']ₑ) ⇀ₑ (.val v =ₑ .val v')) := by
  intro p; simp only [Lemmas.valid_impl]; intro h
  simp [denotation] at h; obtain ⟨⟨h1, h2⟩, ⟨g1, g2⟩⟩ := h
  have q1 : ⊨[μ] ⊡ₑ [echo₂, Term.val v]ₑ := by apply ca.CaOutput?_simp; assumption
  have q2 : ⊨[μ] ⊡ₑ [echo₂, Term.val v']ₑ := by apply ca.CaOutput?_simp; assumption
  have q1' : ⊨[μ] ⟐ₑ ([echo₂, Term.val v]ₑ ∧ₑ [echo₂, Term.val v']ₑ) := by
    intro _; simp only [valid_pred, Lemmas.denotation_contraquorum, denotation]
    apply Theorem_2_4_4.t2'; rw [Lemmas.le_and]; constructor
    · simpa [denotation] using q1 p
    · simpa [denotation] using q2 p
  have c2 : ⊨[μ] (⊡ₑ TF[echo₂]ₑ) := ca.CaCorrect echo₂
  have h3 : ⊨[μ] (Tₑ (◇ₑ ([echo₂, .val v]ₑ ∧ₑ [echo₂, .val v']ₑ))):= by
    intro _; simp [denotation];
    have l : ⊨ (T (◇ (⟦[echo₂, .val v]ₑ ∧ₑ [echo₂, .val v']ₑ⟧ᵈ μ))) := by
         apply Lemma_2_3_7.c3
         · simp
           specialize c2 default; simp [denotation] at c2; obtain ⟨x1, x2, x3⟩ := c2; exists x1
           constructor; assumption; intro k kx1; specialize x3 k kx1; simp [denotation]
           have v1 := x3 v; have v2 := x3 v'; apply Lemmas.byzantine_le_TF_and.mpr
           intro ⟨h1,h2⟩; simp [Lemmas.valid_and_TF h1 v1, Lemmas.valid_and_TF h2 v2]
         · specialize q1' default; rw [valid_pred] at q1'
           simp only [Lemmas.denotation_contraquorum] at q1'; exact q1'
    simpa [denotation] using l
  simp [denotation]
  specialize h3 default; simp [denotation] at h3; obtain ⟨p1, p2⟩ := h3; rw [Lemmas.and_true] at p2
  have u := ca.CaEcho2Affine p1; simp [denotation] at u; specialize u v v'
  simp [Lemmas.neg_and, Lemmas.le_or_implies] at u; apply u p2.1 p2.2

end Proposition_5_3_3

end CA
