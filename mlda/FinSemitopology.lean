import mlda.Base
import mlda.Three

structure FinSemitopology (P : Type) [TopologicalSpace P] [Fintype P] where
  Open : Finset (Finset P)
  subset_P : Open ⊆ (Finset.univ : Finset P).powerset
  all_open : ∀ O ∈ Open, IsOpen (O : Set P)

namespace FinSemitopology

open scoped Three.Function
open Three.Function

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
 
theorem p1_3 : (Three.Atom.neg (◇ (¬ f'))) = □ f := by
  sorry

end Lemma_2_3_3
