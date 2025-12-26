import mlda.Base
import mlda.Three

structure FinSemitopology (P : Type) [TopologicalSpace P] [Fintype P] where
  Open : Finset (Finset P)
  subset_P : Open ⊆ (Finset.univ : Finset P).powerset
  all_open : ∀ O ∈ Open, IsOpen (O : Set P)

namespace FinSemitopology

open scoped Three.Function
open Three.Function
open Three.Atom

variable
  {P : Type}
  [Fintype P]
  [TopologicalSpace P]
  {S : FinSemitopology P}
  (f f' : P → 𝟯)

abbrev ℙ : Finset P := Finset.univ

def Open1 : Finset (Finset P) := S.Open.filter (·.Nonempty)

def everywhere := ⋀ f ℙ
scoped notation "□" => everywhere

def somewhere := ⋁ f ℙ
scoped notation "◇" => somewhere

namespace Lemma_2_3_3

omit [Fintype P] [TopologicalSpace P] in
theorem p1_1 : (¬ (f ∧ f')) = (¬ f ∨ ¬ f') := by
  funext x; simp; cases f x <;> cases f' x <;> simp

omit [Fintype P] [TopologicalSpace P] in
theorem p1_2 : (¬ (f ∨ f')) = (¬ f ∧ ¬ f') := by
  funext x; simp; cases f x <;> cases f' x <;> simp

theorem p1_3 : (¬ (◇ (¬ f'))) = □ f := by
  unfold somewhere everywhere bigAnd bigOr; simp
  cases h : Finset.fold Three.Atom.and Three.true f ℙ
  have k : Finset.fold min Three.true f ℙ ≤ .false := by simp; exact ge_of_eq h.symm
  have y := (Finset.fold_min_le Three.false).mp k
  cases y
  contradiction
  next u =>
    simp at k






end Lemma_2_3_3
