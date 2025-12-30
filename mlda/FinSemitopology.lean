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

def everywhere := ⋀ ℙ f
scoped notation "□" => everywhere

def somewhere := ⋁ ℙ f
scoped notation "◇" => somewhere

def quorum := ⋁ S.Open1 (fun o => ⋀ o f)
scoped notation "⯀" => quorum
notation "⯀" "(" S ")" => quorum (S := S)

def contraquorum := ⋀ S.Open1 (fun o => ⋁ o f)
scoped notation "◆" => contraquorum
notation "◆" "(" S ")" => contraquorum (S := S)

namespace Lemma_2_3_3

open Three.Lemmas

omit [Fintype P] [TopologicalSpace P] in
theorem p1_1 : (¬ (f ∧ f')) = (¬ f ∨ ¬ f') := by
  funext x; unfold Three.Function.neg Three.Function.and Three.Function.or; simp; cases f x <;> cases f' x <;> simp!

omit [Fintype P] [TopologicalSpace P] in
theorem p1_2 : (¬ (f ∨ f')) = (¬ f ∧ ¬ f') := by
  funext x; unfold Three.Function.neg Three.Function.and Three.Function.or; simp; cases f x <;> cases f' x <;> simp!

omit [TopologicalSpace P] in
theorem p1_3 : (¬ (◇ (¬ f))) = □ f := by
  simp [somewhere, everywhere, join_neg, neg_neg];

omit [TopologicalSpace P] in
theorem p1_4 : (¬ (□ (¬ f))) = ◇ f := by
  simp [somewhere, everywhere, meet_neg, neg_neg];

theorem p1_5 : (¬ (◆(S) (¬ f))) = ⯀(S) f := by
  simp_rw [contraquorum, join_neg, neg_fold, meet_neg, neg_neg]; rfl

theorem p1_6 : (¬ (⯀(S) (¬ f))) = ◆(S) f := by
  simp_rw [quorum, meet_neg, neg_fold, join_neg, neg_neg]; rfl

end Lemma_2_3_3
