import mlda.Base
import mlda.Three

-- TODO Semitopologies need not be closed under arbitrary intersections.
-- I've added TopologicalSpace P as a constraint because it already exists in mathlib.
-- It should be replaced at some point to drop the isOpen_inter condition.
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
scoped notation "⊡" => quorum
notation "⊡" "(" S ")" => quorum (S := S)

def contraquorum := ⋀ S.Open1 (fun o => ⋁ o f)
scoped notation "⟐⟐" => contraquorum
notation "⟐" "(" S ")" => contraquorum (S := S)

end

section

variable
  {P : Type}
  [Fintype P]
  {Q : Finset P}
  {f f' : P → 𝟯}
  (a b : 𝟯)

open Three.Lemmas

theorem everywhere_true : □ f = .true ↔ ∀ x, f x = .true := by simp [everywhere, meet_true]

theorem everywhere_byzantine : □ f = .byzantine ↔ (∀ (x : P), Three.byzantine ≤ f x) ∧ ∃ x, f x = Three.byzantine := by
  simp [everywhere]

theorem somewhere_true : ◇ f = .true ↔ ∃ x, f x = .true := by simp [somewhere, join_true]

variable
  [TopologicalSpace P]
  {S : FinSemitopology P}

theorem quorum_true : ⊡(S) f = .true ↔ ∃ s ∈ S.Open1, ∀ x ∈ s, f x = .true := by
  simp [quorum, join_true]

theorem quorum_valid : .byzantine ≤ ⊡(S) f ↔
                       (∃ s ∈ S.Open1, ∀ x ∈ s, Three.byzantine ≤ f x) := by
  simp [quorum, le_join, byzantine_le_meet]

end


namespace Lemma_2_3_3

variable
  {P : Type}
  {f f' : P → 𝟯}
  {a : 𝟯}

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
  : (¬ (⟐(S) (¬ f))) = ⊡(S) f := by
  simp_rw [contraquorum, join_neg, neg_fold, meet_neg, neg_neg]; rfl

theorem p1_6 [Fintype P] [TopologicalSpace P] {S : FinSemitopology P}
  : (¬ (⊡(S) (¬ f))) = ⟐(S) f := by
  simp_rw [quorum, meet_neg, neg_fold, join_neg, neg_neg]; rfl

@[simp] theorem p2_1 : (¬ (T (¬ a))) = TB a := by cases a <;> rfl
@[simp] theorem p2_2 : (¬ (TB (¬ a))) = T a := by cases a <;> rfl

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
  : ⊡(S) (M ∘ f) = M (⊡(S) f) := by
  calc (⋁ Open1 fun o ↦ ⋀ o (M ∘ f)) = ⋁ Open1 fun o ↦ M (⋀ o f) :=
                by conv => lhs; arg 2; intro o; apply map_meet
       _ = M (⋁ S.Open1 fun o ↦ (⋀ o f)) := by apply map_join

theorem map_contraquorum [TopologicalSpace P] [Fintype P] {S : FinSemitopology P} [MapMax M] [MapMin M]
  : ⟐(S) (M ∘ f) = M (⟐(S) f) := by
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

theorem p1 : (□ f ∧ ⊡(S) f') ≤ ⊡(S) (f ∧ f') := by
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
  {f f' : P → 𝟯}
  (a : 𝟯)
  [Fintype P]
  [TopologicalSpace P]
  {S : FinSemitopology P}

theorem p1 : (⊡(S) f ∧ ⟐(S) f') ≤ ◇ (f ∧ f') := by
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

theorem c1 : ⊨ (⊡(S) f ∧ ⟐(S) f') → ⊨ (◇ (f ∧ f')) := by
  intro x; apply le_implies_valid p1 x

-- theorem c2 : ⊨ (⟐(S) f') → ⊨ (◇ f') := by
--   sorry

end Lemma_2_3_7

class Twined3 {P : Type} [TopologicalSpace P] [Fintype P] [DecidableEq P] (S : FinSemitopology P) where
  twined : ∀ (a b c : {x | x ∈ S.Open1}), (a.val ∩ b ∩ c) ∈ S.Open1

export Twined3 (twined)

namespace Theorem_2_4_3

open Three.Lemmas

variable
  {P : Type}
  {f f' : P → 𝟯}
  [Fintype P]
  [DecidableEq P]
  [TopologicalSpace P]
  {S : FinSemitopology P}
  [Twined3 S]

theorem t : (⊡(S) f ∧ ⊡(S) f') ≤ ⟐(S) (f ∧ f') := by
  apply le_by_cases
  case c1 =>
    intro h _; obtain ⟨h1, h2⟩ := and_true.mp h
    have ⟨s1, m1, p1⟩ := join_true.mp h1
    have ⟨s2, m2, p2⟩ := join_true.mp h2
    simp [contraquorum]; intro s3 m3
    have x := twined ⟨_, m1⟩ ⟨_, m2⟩ ⟨_, m3⟩; simp [Open1] at x; rcases x with ⟨x1, w, w1⟩
    simp [Finset.mem_inter] at w1; rcases w1 with ⟨w1, w2, w3⟩
    exists w; constructor; assumption;
    simp [Three.Function.and, Three.Lemmas.and_true]
    exact ⟨meet_true.mp p1 _ w1, meet_true.mp p2 _ w2⟩
  case c2 =>
    intro h _;
    rw [contraquorum, byzantine_le_meet]
    obtain ⟨h1, h2⟩ := byzantine_le_and.mp (ge_of_eq h)
    have ⟨s1, m1, b1⟩ := byzantine_le_join.mp h1
    have ⟨s2, m2, b2⟩ := byzantine_le_join.mp h2
    intro s3 m3;
    simp [byzantine_le_join, Three.Function.and, byzantine_le_and];
    obtain x := twined ⟨_, m1⟩ ⟨_, m2⟩ ⟨_, m3⟩; simp [Open1] at x; rcases x with ⟨_, w, w1⟩
    simp [Finset.mem_inter] at w1; obtain ⟨w1, w2, w3⟩ := w1
    exists w; constructor; assumption; constructor
    exact byzantine_le_meet.mp b1 w w1; exact byzantine_le_meet.mp b2 w w2

-- TODO
-- theorem t' : (⊡(S) f ∧ ⊡(S) f') ≤ ⟐(S) (f ∧ f') → Twined3 S := by
--   intro h ⟨a, ma⟩ ⟨b, mb⟩ ⟨c, mc⟩; simp
--   sorry

end Theorem_2_4_3

namespace Corollary_2_4_4

variable
  {P : Type}
  {f f' : P → 𝟯}
  [Fintype P]
  [DecidableEq P]
  [TopologicalSpace P]
  {S : FinSemitopology P}
  [twined : Twined3 S]

open Three.Lemmas

theorem t1 : ⊡(S) (f ∨ f') ≤ (⟐(S) f ∨ ⟐(S) f') := by
  have x := Proposition_2_2_2.p9.mp (Theorem_2_4_3.t (f := ¬ f) (f' := ¬ f') (S := S))
  simpa [← Lemma_2_3_3.p1_2, Lemma_2_3_3.p1_5, Three.Lemmas.neg_and
        , Lemma_2_3_3.p1_6, Lemma_2_3_3.p1_6] using x

theorem t2 : ⊨ (⊡(S) (f ∨ f')) → ⊨ (⟐(S) f ∨ ⟐(S) f') := Three.Lemmas.le_implies_valid t1

end Corollary_2_4_4

namespace Remark_2_4_5

open Three.Lemmas

variable
  {P : Type}
  {f f' : P → 𝟯}
  [Fintype P]
  [DecidableEq P]
  [TopologicalSpace P]
  {S : FinSemitopology P}
  [twined : Twined3 S]
  (q : ⊨ (⊡(S) (TF f)))

include q
omit [DecidableEq P]
theorem q' : ∃ s ∈ S.Open1, ∀ x ∈ s, ⊨ (TF (f x)) := by
  obtain ⟨s, sm, ps⟩ := by simpa [valid_byzantine_le, quorum_valid] using q
  exists s; constructor; assumption; intro x xm
  simpa [valid_byzantine_le] using ps x xm

include q
theorem t1 : ⊨ (□ f) → ⊨ (T (⊡(S) f)) := by
  have ⟨qs, qm, p⟩ := q' q;
  intro k; simp [quorum_true];
  cases valid_cases.mp k
  next l =>
    exists qs; constructor; assumption
    intro x _; exact everywhere_true.mp l x
  next l =>
    obtain l := (everywhere_byzantine.mp l).1
    exists qs; constructor; assumption; intro x xm
    specialize l x; cases valid_TF.mp (p _ xm); assumption;
    next k => rw [k] at l; contradiction

end Remark_2_4_5
