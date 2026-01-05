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

section

variable
  {P : Type}
  [Fintype P]
  [TopologicalSpace P]
  {Q : Finset P}
  {S : FinSemitopology P}
  (f f' : P → 𝟯)
  (a b : 𝟯)

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

end

namespace Lemma_2_3_3

variable
  {P : Type}
  (f f' : P → 𝟯)
  (a : 𝟯)

open Three.Lemmas

theorem p1_1 : (¬ (f ∧ f')) = (¬ f ∨ ¬ f') := by
  funext x; unfold Three.Function.neg Three.Function.and Three.Function.or; simp; cases f x <;> cases f' x <;> simp!

theorem p1_2 : (¬ (f ∨ f')) = (¬ f ∧ ¬ f') := by
  funext x; unfold Three.Function.neg Three.Function.and Three.Function.or; simp; cases f x <;> cases f' x <;> simp!

theorem p1_3 [Fintype P] : (¬ (◇ (¬ f))) = □ f := by
  simp [somewhere, everywhere, join_neg, neg_neg];

theorem p1_4 [Fintype P] : (¬ (□ (¬ f))) = ◇ f := by
  simp [somewhere, everywhere, meet_neg, neg_neg];

theorem p1_5 [Fintype P] [TopologicalSpace P] {S : FinSemitopology P}
  : (¬ (◆(S) (¬ f))) = ⯀(S) f := by
  simp_rw [contraquorum, join_neg, neg_fold, meet_neg, neg_neg]; rfl

theorem p1_6 [Fintype P] [TopologicalSpace P] {S : FinSemitopology P}
  : (¬ (⯀(S) (¬ f))) = ◆(S) f := by
  simp_rw [quorum, meet_neg, neg_fold, join_neg, neg_neg]; rfl

@[simp] theorem p2_1 : (¬ (T (¬ a))) = TB a := by cases a <;> rfl
@[simp] theorem p2_2 : (¬ (TB (¬ a))) = T a := by cases a <;> rfl

-- NOTE this theorem is in the paper but it is incorrect. E.g. a = b = byzantine
-- theorem p3 : (a ⇀ b) = ((TB (¬ b)) ⇀ (TB (¬ a))) := by sorry

end Lemma_2_3_3

namespace Remark_2_3_5

variable
  {P : Type}
  (f : P → 𝟯)
  (a : 𝟯)

open Three
open Three.Atom

@[simp] theorem T_idempotent : T (T a) = T a := by cases a <;> rfl
@[simp] theorem TB_idempotent : TB (TB a) = TB a := by cases a <;> rfl

class PreservesTruth (M : 𝟯 → 𝟯) where
  map_true : M true = Three.true := by rfl
  map_false : M false = Three.false := by rfl

instance : PreservesTruth T where
instance : PreservesTruth TB where

instance : MapMin T where
  map_min := by intro a b; cases a <;> cases b <;> rfl

instance : MapMax T where
  map_max := by intro a b; cases a <;> cases b <;> rfl

variable
  (M : 𝟯 → 𝟯) -- In this section M stands for T and TB
  {Q : Finset P}
  [PreservesTruth M]

theorem map_meet [MapMin M]
  : ⋀ Q (M ∘ f) = M (⋀ Q f) := by
  simpa [PreservesTruth.map_true] using Finset.fold_hom (b := Three.true) (m := M) map_min

theorem map_join [MapMax M]
  : ⋁ Q (M ∘ f) = M (⋁ Q f) := by
  simpa [PreservesTruth.map_false] using Finset.fold_hom (b := Three.false) (m := M) map_max

theorem map_everywhere [Fintype P] [MapMin M]
  : □ (M ∘ f) = M (□ f) := by
  simpa [PreservesTruth.map_true] using Finset.fold_hom (b := Three.true) (m := M) map_min

theorem map_somewhere [Fintype P] [MapMax M] : ◇ (M ∘ f) = M (◇ f) := by
  simpa [PreservesTruth.map_false] using Finset.fold_hom (b := Three.false) (m := M) map_max

theorem map_quorum [TopologicalSpace P] [Fintype P] {S : FinSemitopology P} [MapMax M] [MapMin M]
  : ⯀(S) (M ∘ f) = M (⯀(S) f) := by
  calc (⋁ Open1 fun o ↦ ⋀ o (M ∘ f)) = ⋁ Open1 fun o ↦ M (⋀ o f) :=
                by conv => lhs; arg 2; intro o; apply map_meet
       _ = M (⋁ S.Open1 fun o ↦ (⋀ o f)) := by apply map_join

theorem map_contraquorum [TopologicalSpace P] [Fintype P] {S : FinSemitopology P} [MapMax M] [MapMin M]
  : ◆(S) (M ∘ f) = M (◆(S) f) := by
  calc (⋀ Open1 fun o ↦ ⋁ o (M ∘ f)) = ⋀ Open1 fun o ↦ M (⋁ o f) :=
                by conv => lhs; arg 2; intro o; apply map_join
       _ = M (⋀ S.Open1 fun o ↦ (⋁ o f)) := by apply map_meet (M := M)

end Remark_2_3_5

namespace Lemma_2_3_6

variable
  {P : Type}
  (f f' : P → 𝟯)
  (a : 𝟯)
  [Fintype P]
  [TopologicalSpace P]
  {S : FinSemitopology P}

open Three.Lemmas

theorem p1 : (□ f ∧ ⯀(S) f') ≤ ⯀(S) (f ∧ f') := by
  apply le_by_cases
  case c1 =>
    intro h1 _
    obtain ⟨h1, h2⟩ := and_true.mp h1
    obtain ⟨u, mu, pu⟩ := join_true.mp h2
    obtain pf := meet_true.mp h1
    obtain pf' := meet_true.mp pu
    rw [quorum, join_true]; exists u; constructor; assumption;
    simp [meet_true]; intro y py; simp [Three.Function.and, Three.Lemmas.and_true]
    exact ⟨pf y (Finset.mem_univ y), pf' y py⟩
  case c2 =>
    intro h1 _
    obtain ⟨h1, h2⟩ := byzantine_le_and.mp (ge_of_eq h1)
    obtain h1 := byzantine_le_meet.mp h1
    obtain ⟨u, mu, pu⟩ := byzantine_le_join.mp h2
    obtain pu := byzantine_le_meet.mp pu
    rw [quorum, byzantine_le_join]; exists u; constructor; assumption
    simp [byzantine_le_meet]; intro x xu; simp [Three.Function.and, byzantine_le_and]
    exact ⟨h1 x (Finset.mem_univ x), pu x xu⟩

end Lemma_2_3_6

namespace Lemma_2_3_7

open Three.Lemmas

variable
  {P : Type}
  (f f' : P → 𝟯)
  (a : 𝟯)
  [Fintype P]
  [TopologicalSpace P]
  {S : FinSemitopology P}

theorem p1 : (⯀(S) f ∧ ◆(S) f') ≤ ◇ (f ∧ f') := by
  apply le_by_cases;
  case c1 =>
    intro h1 _
    obtain ⟨h1, h2⟩ := and_true.mp h1
    obtain ⟨s, ms, ps⟩ := join_true.mp h1
    obtain ⟨u, mu, pu⟩ := join_true.mp (meet_true.mp h2 s ms)
    simp [somewhere, join_true]; exists u; simp [Three.Function.and, Three.Lemmas.and_true];
    constructor; exact meet_true.mp ps u mu; assumption
  case c2 =>
    intro h1 _
    simp [somewhere, byzantine_le_join]
    obtain ⟨h1, h2⟩ := byzantine_le_and.mp (ge_of_eq h1)
    obtain ⟨s, ms, ps⟩ := byzantine_le_join.mp h1
    obtain ⟨u, u1, f'u⟩ := byzantine_le_join.mp (byzantine_le_meet.mp h2 s ms)
    have fu := byzantine_le_meet.mp ps _ u1
    exists u; simp [Three.Function.and, le_and];
    exact ⟨fu, f'u⟩

end Lemma_2_3_7
