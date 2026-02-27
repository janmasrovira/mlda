import mlda.Base
import mlda.Three

structure FinSemitopology (P : Type) [Nonempty P] [DecidableEq P] [Fintype P] where
  Open : Finset (Finset P)
  empty_open : ∅ ∈ Open
  univ_open : Fintype.elems ∈ Open
  subset_P : Open ⊆ Fintype.elems.powerset
  isOpen_sUnion : ∀ s : Finset (Finset P), (∀ t ∈ s, t ∈ Open) → s.biUnion id ∈ Open

namespace FinSemitopology

open scoped Three.Function
open Three.Atom

section

variable
  {P : Type}
  [Fintype P]
  [Nonempty P]
  [DecidableEq P]
  {Q : Finset P}
  {S : FinSemitopology P}
  (f f' : P → 𝟯)
  (a b : 𝟯)

abbrev ℙ : Finset P := Finset.univ

def Open1 : Finset (Finset P) := S.Open.filter (·.Nonempty)

def univ_in_Open1 : Finset.univ ∈ S.Open1 := by
  simp [Open1]; exact S.univ_open

abbrev everywhere := ⋀ ℙ f
scoped notation "□" => everywhere

abbrev somewhere := ⋁ ℙ f
scoped notation "◇" => somewhere

abbrev quorum := ⋁ S.Open1 (fun o => ⋀ o f)
scoped notation "⊡" => quorum
scoped notation "⊡" "(" A ")" => quorum (S := A)

abbrev contraquorum := ⋀ S.Open1 (fun o => ⋁ o f)
scoped notation "⟐" => contraquorum
scoped notation "⟐" "(" A ")" => contraquorum (S := A)

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
  [DecidableEq P]
  [Nonempty P]
  {S : FinSemitopology P}

theorem quorum_true : ⊡(S) f = .true ↔ ∃ s ∈ S.Open1, ∀ x ∈ s, f x = .true := by
  simp [quorum]

theorem quorum_valid : .byzantine ≤ ⊡(S) f ↔
                       (∃ s ∈ S.Open1, ∀ x ∈ s, Three.byzantine ≤ f x) := by
  simp [quorum, le_join, byzantine_le_meet]

theorem contraquorum_true : ⟐(S) f = .true ↔ ∀ s ∈ S.Open1, ∃ x ∈ s, f x = .true := by
  simp [contraquorum]

end

namespace Lemma_2_3_3

variable
  {P : Type}
  {f f' : P → 𝟯}
  {a : 𝟯}

open Three.Lemmas

theorem p1_1 : (¬ᶠ (f ∧ f')) = (¬ᶠ f ∨ ¬ᶠ f') := by
  funext x; unfold Three.Function.neg Three.Function.and Three.Function.or; simp; cases f x <;> cases f' x <;> simp!

theorem p1_2 : (¬ᶠ (f ∨ f')) = (¬ᶠ f ∧ ¬ᶠ f') := by
  funext x; unfold Three.Function.neg Three.Function.and Three.Function.or; simp

theorem p1_3 [Fintype P] : (¬ (◇ (¬ᶠ f))) = □ f := by
  simp [somewhere, everywhere, join_neg];

theorem p1_4 [Fintype P] : (¬ (□ (¬ᶠ f))) = ◇ f := by
  simp [somewhere, everywhere, meet_neg];

theorem p1_5 [Nonempty P] [Fintype P] [DecidableEq P] {S : FinSemitopology P}
  : (¬ (⟐(S) (¬ᶠ f))) = ⊡(S) f := by
  simp [contraquorum, join_neg, Three.Function.neg_fold, meet_neg]

theorem p1_6 [Nonempty P] [Fintype P] [DecidableEq P] {S : FinSemitopology P}
  : (¬ (⊡(S) (¬ᶠ f))) = ⟐(S) f := by
  simp [quorum, meet_neg, Three.Function.neg_fold, join_neg]

@[simp] theorem p2_1 : (¬ (T (¬ a))) = TB a := by cases a <;> rfl
@[simp] theorem p2_2 : (¬ (TB (¬ a))) = T a := by cases a <;> rfl

end Lemma_2_3_3

namespace Remark_2_3_5

variable
  {P : Type}
  {f : P → 𝟯}
  {a : 𝟯}

open Three
open scoped Three.Atom

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

theorem map_quorum [Nonempty P] [DecidableEq P] [Fintype P] {S : FinSemitopology P} [MapMax M] [MapMin M]
  : ⊡(S) (M ∘ f) = M (⊡(S) f) := by
  calc (⋁ Open1 fun o ↦ ⋀ o (M ∘ f)) = ⋁ Open1 fun o ↦ M (⋀ o f) :=
                by conv => lhs; arg 2; intro o; apply map_meet
       _ = M (⋁ S.Open1 fun o ↦ (⋀ o f)) := by apply map_join

theorem map_contraquorum [Nonempty P] [DecidableEq P] [Fintype P] {S : FinSemitopology P} [MapMax M] [MapMin M]
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
  [Nonempty P]
  [DecidableEq P]
  {S : FinSemitopology P}

open Three.Lemmas

theorem t1 : (□ f ∧ ⊡(S) f') ≤ ⊡(S) (f ∧ f') := by
  apply le_by_cases
  case c1 =>
    intro h1 _
    obtain ⟨h1, h2⟩ := and_true.mp h1
    obtain ⟨u, mu, pu⟩ := join_true.mp h2
    obtain pf := meet_true.mp h1
    obtain pf' := meet_true.mp pu
    rw [quorum, join_true]; exists u; constructor; assumption;
    simp [meet_true]; intro y py; simp [Three.Lemmas.and_true]
    exact ⟨pf y (Finset.mem_univ y), pf' y py⟩
  case c2 =>
    intro h1 _
    obtain ⟨h1, h2⟩ := byzantine_le_and.mp (ge_of_eq h1)
    obtain h1 := byzantine_le_meet.mp h1
    obtain ⟨u, mu, pu⟩ := byzantine_le_join.mp h2
    obtain pu := byzantine_le_meet.mp pu
    rw [quorum, byzantine_le_join]; exists u; constructor; assumption
    simp [byzantine_le_meet]; intro x xu; simp [byzantine_le_and]
    exact ⟨h1 x (Finset.mem_univ x), pu x xu⟩

theorem t2 : ⊨ (□ f ∧ ⊡(S) f') → ⊨ (⊡(S) (f ∧ f')) := by
  apply le_implies_valid; apply t1

theorem t3 : ⊨ (□ f ∧ ⊡(S) (TF ∘ f)) → ⊨ (T (⊡(S) f)) := by
  have b : ⊨ (□ f ∧ ⊡(S) (TF ∘ f)) → ⊨ (⊡(S) (f ∧ (TF ∘ f))) := t2 (f' := TF ∘ f) (f := f)
  intro h; have h' := b h
  simp at h' ⊢; obtain ⟨h1, h2, h3⟩ := h'
  refine ⟨_, h2, ?_⟩; intro _ ym; specialize h3 _ ym; rw [le_and] at h3
  apply valid_and_TF h3.1 h3.2

end Lemma_2_3_6

namespace Lemma_2_3_7

open Three.Lemmas

variable
  {P : Type}
  {f f' : P → 𝟯}
  (a : 𝟯)
  [Fintype P]
  [Nonempty P]
  [topo : DecidableEq P]
  {S : FinSemitopology P}

theorem p1 : (⊡(S) f ∧ ⟐(S) f') ≤ ◇ (f ∧ f') := by
  apply le_by_cases
  case c1 =>
    intro h1 _
    obtain ⟨h1, h2⟩ := and_true.mp h1
    obtain ⟨s, ms, ps⟩ := join_true.mp h1
    obtain ⟨u, mu, pu⟩ := join_true.mp (meet_true.mp h2 s ms)
    simp [somewhere, join_true]; exists u; simp [Three.Lemmas.and_true];
    constructor; exact meet_true.mp ps u mu; assumption
  case c2 =>
    intro h1 _
    simp [somewhere, byzantine_le_join]
    obtain ⟨h1, h2⟩ := byzantine_le_and.mp (ge_of_eq h1)
    obtain ⟨s, ms, ps⟩ := byzantine_le_join.mp h1
    obtain ⟨u, u1, f'u⟩ := byzantine_le_join.mp (byzantine_le_meet.mp h2 s ms)
    have fu := byzantine_le_meet.mp ps _ u1
    exists u; simp [le_and];
    exact ⟨fu, f'u⟩

theorem c1 : ⊨ (⊡(S) f ∧ ⟐(S) f') → ⊨ (◇ (f ∧ f')) := by
  intro x; apply le_implies_valid p1 x

theorem c2 : ⊨ (⟐(S) f) → ⊨ (◇ f) := by
  intro p
  simp [somewhere, le_join]
  simp [contraquorum, le_meet] at p
  have y := p Finset.univ ?_
  simp at y; exact y
  simp [Open1]; exact S.univ_open

theorem c3 : ⊨ (⊡(S) (TF ∘ f)) → ⊨ (⟐(S) f) → ⊨ (T (◇ f)) := by
  intro h g; rw [Valid] at h g; have l := le_and.mpr ⟨h, g⟩
  have y := c1 l; simp at y; obtain ⟨y1, y2⟩ := y; simp [le_and] at y2; obtain ⟨y2, y3⟩ := y2
  simp; exists y1; exact valid_and_TF y3 y2

end Lemma_2_3_7

class Twined3 {P : Type} [Nonempty P] [DecidableEq P] [Fintype P] [DecidableEq P] (S : FinSemitopology P) where
  twined : ∀ {a b c}, a ∈ S.Open1 → b ∈ S.Open1 → c ∈ S.Open1 → a ∩ b ∩ c ∈ S.Open1

export Twined3 (twined)

namespace Example_2_4_3
-- TODO
end Example_2_4_3

namespace Theorem_2_4_4

open Three.Lemmas

variable
  {P : Type}
  {f f' : P → 𝟯}
  [Nonempty P]
  [Fintype P]
  [DecidableEq P]
  {S : FinSemitopology P}
  [Twined3 S]

theorem t : (⊡(S) f ∧ ⊡(S) f') ≤ ⟐(S) (f ∧ f') := by
  apply le_by_cases
  case c1 =>
    intro h _; obtain ⟨h1, h2⟩ := and_true.mp h
    have ⟨s1, m1, p1⟩ := join_true.mp h1
    have ⟨s2, m2, p2⟩ := join_true.mp h2
    simp [contraquorum]; intro s3 m3
    have x := twined m1 m2 m3; simp [Open1] at x; rcases x with ⟨x1, w, w1⟩
    simp [Finset.mem_inter] at w1; rcases w1 with ⟨w1, w2, w3⟩
    exists w; constructor; assumption;
    simp [Three.Lemmas.and_true]
    exact ⟨meet_true.mp p1 _ w1, meet_true.mp p2 _ w2⟩
  case c2 =>
    intro h _;
    rw [contraquorum, byzantine_le_meet]
    obtain ⟨h1, h2⟩ := byzantine_le_and.mp (ge_of_eq h)
    have ⟨s1, m1, b1⟩ := byzantine_le_join.mp h1
    have ⟨s2, m2, b2⟩ := byzantine_le_join.mp h2
    intro s3 m3;
    simp [byzantine_le_join, Three.Function.and, byzantine_le_and];
    obtain x := twined m1 m2 m3; simp [Open1] at x; rcases x with ⟨_, w, w1⟩
    simp [Finset.mem_inter] at w1; obtain ⟨w1, w2, w3⟩ := w1
    exists w; constructor; assumption; constructor
    exact byzantine_le_meet.mp b1 w w1; exact byzantine_le_meet.mp b2 w w2

theorem t' : ⊡(S) f ≤ ⟐(S) f := by
  simpa using t (f := f) (f' := f)

theorem t'' : ⊨ (⊡(S) f) → ⊨ (⟐(S) f) := by
  apply le_implies_valid t'

theorem t2 : ⊨ (⊡(S) f ∧ ⊡(S) f') → (⊨ (⟐(S) (f ∧ f'))) := by
  apply le_implies_valid t

theorem t2' : .byzantine ≤ (⊡(S) f ∧ ⊡(S) f') → (⊨ (⟐(S) (f ∧ f'))) := by
  apply le_implies_valid t

end Theorem_2_4_4

namespace Corollary_2_4_5

variable
  {P : Type}
  {f f' : P → 𝟯}
  [Nonempty P]
  [Fintype P]
  [DecidableEq P]
  {S : FinSemitopology P}
  [twined : Twined3 S]

open Three.Lemmas

theorem t1 : ⊡(S) (f ∨ f') ≤ (⟐(S) f ∨ ⟐(S) f') := by
  have x := Proposition_2_2_2.p9.mp (Theorem_2_4_4.t (f := ¬ᶠ f) (f' := ¬ᶠ f') (S := S))
  simpa [← Lemma_2_3_3.p1_2, Lemma_2_3_3.p1_5, Three.Lemmas.neg_and
        , Lemma_2_3_3.p1_6, Lemma_2_3_3.p1_6] using x

theorem t2 : ⊨ (⊡(S) (f ∨ f')) → ⊨ (⟐(S) f ∨ ⟐(S) f') := Three.Lemmas.le_implies_valid t1

end Corollary_2_4_5

namespace Remark_2_4_6

open Three.Lemmas

variable
  {P : Type}
  {f f' : P → 𝟯}
  [Fintype P]
  [Nonempty P]
  [DecidableEq P]
  {S : FinSemitopology P}
  (q : ⊨ (⊡(S) (TF ∘ f)))

include q in
theorem q' : ∃ s ∈ S.Open1, ∀ x ∈ s, ⊨ (TF (f x)) := by
  obtain ⟨s, sm, ps⟩ := by simpa [quorum_valid] using q;
  exists s

include q in
theorem t1 : ⊨ (□ f) → ⊨ (T (⊡(S) f)) := by
  have ⟨qs, qm, p⟩ := q' q;
  intro k; simp;
  cases valid_cases.mp k
  next l =>
    exists qs; constructor; assumption
    intro x _; exact everywhere_true.mp l x
  next l =>
    obtain l := (everywhere_byzantine.mp l).1
    exists qs; constructor; assumption; intro x xm
    specialize l x; cases valid_TF.mp (p _ xm); assumption;
    next k => rw [k] at l; contradiction

include q in
theorem valid_quorum_implies_true [twined : Twined3 S]
  : ⊨ (⊡(S) f) -> ⊡(S) f = Three.true := by
  intro h; simp [quorum, le_join] at h; obtain ⟨h1, h2, h3⟩ := h
  have ⟨qs, qm, p⟩ := q' q; simp
  refine ⟨qs ∩ h1, ?_, ?_⟩;
  have t := twined.twined qm qm h2; simpa using t
  intro x xq; obtain ⟨x1, x2⟩ := by simpa [Finset.mem_inter] using xq
  cases valid_TF.mp (p x x1); assumption
  next h => have := h3 _ x2; rw [h] at this; contradiction

include q in
theorem t2 [twined : Twined3 S] : ⊨ (⊡(S) f) -> ⊨ (T (⟐(S) f)) := by
  have h := Theorem_2_4_4.t (f := T ∘ f) (f' := T ∘ f) (S := S)
  intro p; replace p := valid_quorum_implies_true q p
  simpa [Remark_2_3_5.map_contraquorum, Remark_2_3_5.map_quorum, p] using h

include q in
theorem t3 : ⊨ (⟐(S) f) → ⊨ (T (◇ f)) := by
  intro k;
  have ⟨qs, qm, p⟩ := q' q
  simp [somewhere]
  simp [contraquorum, le_meet, le_join] at k
  obtain ⟨y, ym, yp⟩ := k _ qm; exists y
  cases valid_TF.mp (p _ ym); assumption
  next h => rw [h] at yp; contradiction

-- TODO I've adapted the statement
theorem t4 : ⊨ ((⊡(S) f) ∧ ⟐(S) (T ∘ f')) → ⊨ (T (◇ f')) := by
  intro h
  have y := Lemma_2_3_7.c1 (S := S) (f := f) h
  obtain ⟨y, yp⟩ := by simpa [somewhere, le_join] using y
  obtain ⟨_, yp⟩ := by simpa [le_and] using yp
  simp [Valid]; exists y

omit q in
theorem t5_1 [twined : Twined3 S] : ⊨ (⊡(S) f ∧ ⊡(S) f') → ⊨ (⟐(S) (f ∧ f')) := by
  simp; intro h
  obtain ⟨h1, h2⟩ := le_and.mp h
  simp [quorum, le_join] at h1 h2
  replace ⟨h1, h1m, h1p⟩ := h1
  replace ⟨h2, h2m, h2p⟩ := h2
  intro w wm
  obtain ⟨k, ⟨lm, l⟩⟩ := by simpa [Open1] using twined.twined h1m h2m wm
  simp [Finset.mem_inter] at l
  refine ⟨lm, l.2.2, ?_⟩; simp [le_and]; constructor
  exact h1p _ l.1; exact h2p _ l.2.1

omit q in
theorem t5_11 [twined : Twined3 S] : ⊨ (⊡(S) f ∧ ⊡(S) f') → ⊨ (⟐(S) (f ∧ f')) :=
  le_implies_valid Theorem_2_4_4.t

omit q in
theorem t5_2 [twined : Twined3 S] : ⊨ (⊡(S) (f ∨ f')) → ⊨ (⟐(S) f ∨ ⟐(S) f') := by
  intro p; exact Corollary_2_4_5.t2 p

end Remark_2_4_6

namespace Remark_2_4_7

-- TODO
-- theorem t' : (∀ f f',(⊡(S) f ∧ ⊡(S) f') ≤ ⟐(S) (f ∧ f')) → Twined3 S := by

end Remark_2_4_7

section

variable
  {P : Type}
  [Fintype P]
  [Nonempty P]
  [DecidableEq P]
  {S : FinSemitopology P}
  {vote observe : P → 𝟯}

class ThyVote (S : FinSemitopology P) (vote observe : P → 𝟯) where
  observe? p : (observe p → ⊡(S) vote) = .true
  observe! p : (⊡(S) vote ⇀ observe p) = .true
  correct : ⊡(S) (TF ∘ vote) = .true
  observeN? p : (¬ (observe p) → ⊡(S) (¬ᶠ vote)) = .true
  observeN! p : (⊡(S) (¬ᶠ vote) ⇀ (¬ (observe p))) = .true
  twined3 f f' : (⊡(S) f ∧ ⊡(S) f') ≤ ⟐(S) (f ∧ f')

end

namespace Lemma_2_5_6

variable
  {P : Type}
  [Fintype P]
  [Nonempty P]
  [DecidableEq P]
  {S : FinSemitopology P}
  {vote observe : P → 𝟯}
  [i : ThyVote S vote observe]

open Three.Lemmas

theorem t1 : ⊨ (◇ observe → ⊡(S) vote) := by
  rw [Proposition_2_2_2.p4]; intro h; obtain ⟨x, t⟩ := somewhere_true.mp h
  simp [quorum, le_join, le_meet]
  obtain ⟨s, xo, sp⟩ := by simpa [quorum] using mp_weak (i.observe? x) (byzantine_le.mpr (.inr t))
  refine ⟨_, xo, ?_⟩; intro y ys; simp [sp _ ys]

theorem t2 : ⊨ (⊡(S) vote ⇀ □ observe) := by
  rw [Proposition_2_2_2.p5, everywhere]; intro h;
  simp; intro p; exact mp_strong_true (i.observe! p) h

theorem t3 : ⊨ (◇ (¬ᶠ observe) → ⊡(S) (¬ᶠ vote)) := by
  rw [Proposition_2_2_2.p4]; intro h; obtain ⟨x, t⟩ := somewhere_true.mp h
  simp [quorum, le_join, le_meet]
  obtain ⟨s, xo, sp⟩ := by simpa [quorum] using mp_weak (i.observeN? x) (byzantine_le.mpr (.inr t))
  refine ⟨_, xo, ?_⟩; intro y ys; simp [sp _ ys]

theorem t4 : ⊨ (⊡(S) vote ⇀ □ observe) := by
  rw [Proposition_2_2_2.p5, everywhere]; intro h;
  simp; intro p; exact mp_strong_true (i.observe! p) h

end Lemma_2_5_6

namespace Proposition_2_5_7

variable
  {P : Type}
  [Fintype P]
  [e : Nonempty P]
  [DecidableEq P]
  {S : FinSemitopology P}
  {vote observe : P → 𝟯}
  [i : ThyVote S vote observe]

open Three.Lemmas

include i in
theorem t : ⊭ (◇ (T ∘ observe) ∧ ◇ (T ∘ (¬ᶠ observe))) := by
  apply notValid_by_contra
  intro h; rw [Valid, le_and] at h; have ⟨h1, h2⟩ := h
  simp [Remark_2_3_5.map_somewhere] at h1 h2
  have ⟨p, px⟩ := h1; have ⟨p', px'⟩ := h2
  have votep := mp_weak (i.observe? p) (byzantine_le.mpr (.inr px))

  have votep' := mp_weak (i.observeN? p') (by simp [px'])
  have q : (⊡(S) vote ∧ ⊡(S) (¬ᶠ vote)) = .true :=
    Three.Lemmas.and_true.mpr ⟨votep, votep'⟩
  have v : (⟐(S) (vote ∧ (¬ᶠ vote))) = .true := by
    have x := i.twined3 vote (¬ᶠ vote); simpa [q] using x
  rw [contraquorum, meet_true] at v
  have k : ⊨ (⟐(S) (B ∘ vote)) := by -- TODO simplify?
    simp [contraquorum, le_meet]; intro s sm
    have ⟨y, ym, yp⟩ := join_true.mp (v _ sm)
    refine ⟨_, ym, ?_⟩
    simp [Three.Function.and] at yp
    apply Proposition_2_2_2.p7 (a := vote y) |>.mp
    simp [yp]
  have c : ⊡(S) (TF ∘ vote) = .true := i.correct
  have kc : ⊨ (⊡(S) (TF ∘ vote) ∧ (⟐(S) (B ∘ vote))) := by
    rw [Valid, le_and]; constructor; simp [c]; exact k
  have r := Lemma_2_3_7.c1 kc
  simp [somewhere, le_join] at r

end Proposition_2_5_7
