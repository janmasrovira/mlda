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

inductive BBSig where
  | broadcast
  | echo
  | ready
  | deliver

export BBSig (broadcast echo ready deliver)

class ThyBB (μ : Model BBSig P V) where
  BrDeliver? : ⊨[μ] ∀ₑ ([deliver]ₑ →ₑ ⊡ₑ [ready]ₑ)
  BrReady? : ⊨[μ] ∀ₑ ([ready]ₑ →ₑ ⊡ₑ [echo]ₑ)
  BrEcho? : ⊨[μ] ∀ₑ ([echo]ₑ →ₑ ◇ₑ [broadcast]ₑ)
  BrDeliver! : ⊨[μ] ∀ₑ (⊡ₑ [ready]ₑ →ₑ [deliver]ₑ)
  BrReady! : ⊨[μ] ∀ₑ (⊡ₑ [echo]ₑ →ₑ [ready]ₑ)
  BrEcho! : ⊨[μ] ∀ₑ (◇ₑ [broadcast]ₑ →ₑ ∃⁎ₑ [echo]ₑ)
  BrReady!! : ⊨[μ] ∀ₑ (⟐ₑ [ready]ₑ →ₑ [ready]ₑ)
  BrEcho01 : ⊨[μ] ∃₀₁ₑ [echo]ₑ
  BrBroadast1 : ⊨[μ] ∃₁ₑ (◇ₑ [broadcast]ₑ)
  BrCorrect : ⊨[μ] ∀ₑ (⊡ₑ TF[ready]ₑ ∧ₑ ⊡ₑ TF[echo]ₑ)
  BrCorrectReady : ⊨[μ] ∀ₑ (TF[ready]ₑ ∨ₑ B[ready]ₑ) -- BrCorrect'
  BrCorrectEcho : ⊨[μ] ∀ₑ (TF[echo]ₑ ∨ₑ B[echo]ₑ) -- BrCorrect'
  BrCorrectBroadcast : ⊨[μ] (□ₑ TF[broadcast]ₑ ∨ₑ □ₑ B[broadcast]ₑ) -- BrCorrect''

namespace ThyBB

  variable
  {μ : Model BBSig P V}
  [bb : ThyBB μ]

theorem BrDeliver!' {p} {v} : (⊨[μ] Tₑ (⊡ₑ [ready, .val v]ₑ)) → .byzantine ≤ μ.ς deliver p v := by
  intro h; have b := bb.BrDeliver!
  specialize b p; rw [Lemmas.valid_forall] at b; specialize b v
  simp only [substSimp, Lemmas.valid_impl] at b
  conv at b => rhs; simp [denotation]
  apply b; specialize h p; rw [Lemmas.valid_T] at h; exact h

theorem BrDeliver?' {p} {v} : μ.ς deliver p v = .true → ⊨[μ] (⊡ₑ [ready, .val v]ₑ) := by
  have b := bb.BrDeliver? p; simp only [Lemmas.valid_forall, substSimp] at b; specialize b v
  rw [Lemmas.substAt_bound, Lemmas.valid_impl] at b
  intro h; exact quorum_global'.mp (b (by simpa [denotation] using h))

theorem BrReady!!' {v} : (⊨[μ] Tₑ (⟐ₑ [ready, .val v]ₑ)) → ⊨[μ] [ready, .val v]ₑ := by
   intro h p;
   have b := bb.BrReady!! p
   simp only [Lemmas.valid_forall] at b; specialize b v; simp only [substSimp, Lemmas.valid_impl] at b
   conv at b => right; simp [substSimp, Term.substAt]
   apply b; specialize h p; simp only [Lemmas.valid_T] at h
   simp [denotation] at h ⊢; exact h

theorem BrCorrectTFReady : ∀ v, ⊨[μ] ⊡ₑ (TFₑ [ready, .val v]ₑ) := by
  intro v p
  have b := Lemmas.valid_forall.mp (bb.BrCorrect p) v
  simp only [substSimp] at b; replace b := Lemmas.valid_and.mp b |>.1
  rw [TF_all] at b
  simp [denotation] at b; obtain ⟨b1, b2, b3⟩ := b
  simp [denotation]; refine ⟨b1, b2, ?_⟩; intro x xb1
  exact b3 x xb1 v

theorem BrCorrectTFEcho : ∀ p, ∀ v, p ⊨[μ] ⊡ₑ (TFₑ [echo, .val v]ₑ) := by
  intro p v
  have b := Lemmas.valid_forall.mp (bb.BrCorrect p) v
  simp only [substSimp] at b; replace b := Lemmas.valid_and.mp b |>.2
  rw [TF_all] at b
  simp [denotation] at b; obtain ⟨b1, b2, b3⟩ := b
  simp [denotation]; refine ⟨b1, b2, ?_⟩; intro x xb1
  exact b3 x xb1 v

end ThyBB

end

namespace Lemma_4_2_4

variable
  {V P : Type}
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  [Fintype V]
  [DecidableEq V]
  (μ : Model BBSig P V)
  [bb : ThyBB μ]
  {p : P}
  {v : V}

abbrev P1 := (⊨[μ] TF[.broadcast]ₑ) ∧
             ∃! v, ∀ p, p ⊨[μ] (Tₑ (◇ₑ [broadcast, .val v]ₑ))

abbrev P2 := ∀ v, ∀ p, p ⊨[μ] Bₑ [broadcast, .val v]ₑ

theorem t : P1 μ ∨ P2 μ := by
  simp [P1, P2]
  cases Lemmas.valid_or.mp (bb.BrCorrectBroadcast default)
  · next h => left; constructor
              · intro p; simp [denotation, existence] at *; intro v;
                simp [Lemmas.byzantine_le_TF]
                intro x; have k := Lemmas.byzantine_le_TF.mp (h p v); contradiction
              · have b := bb.BrBroadast1 default
                simp [denotation, existence, Lemmas.le_and] at b
                have ⟨⟨v, p, b1⟩, b2⟩ := b; clear b
                exists v; simp [denotation] at h ⊢;
                have : Model.ς μ broadcast p v = .true := by
                  specialize h p; simp [Lemmas.byzantine_le_TF] at h
                  cases Lemmas.byzantine_le.mp b1;
                  · next g => specialize h v; contradiction
                  · next g => assumption
                constructor
                · exists p
                · intro u p fx; specialize b2 u v;
                  simp [Lemmas.le_or_implies] at b2; apply_rules
  · next h => right; intro v p; simp [denotation];
              simp [denotation, FinSemitopology.everywhere, existence] at h
              exact h p v

end Lemma_4_2_4

namespace Lemmas

variable
  {V P : Type}
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  [Fintype V]
  [DecidableEq V]
  {μ : Model BBSig P V}
  [bb : ThyBB μ]
  {p p' : P}
  {v v' : V}

-- This lemma is similar to Lemma 4.2.6 in the pdf
theorem when_broadcast : μ.ς broadcast p v = .true →
  Lemma_4_2_4.P1 μ ∧
  ∀ {v' : V} {p' : P}, μ.ς broadcast p' v' = .true → v' = v := by
  intro h; cases Lemma_4_2_4.t μ
  next k => constructor
            · assumption
            · intro v' p' b; obtain ⟨k1, k2, k3, k4⟩ := k
              have f {vy} {py} (hy : μ.ς broadcast py vy = Three.true) : vy = k2 := by
                apply k4; intro ignore; simp [denotation]; exists py
              have := f h; have := f b; subst_vars; rfl
  next k => simp [Lemma_4_2_4.P2, denotation] at k; specialize k v p; rw [h] at k; contradiction

theorem broadcast_true : μ.ς broadcast p v = .true
        → byzantine ≤ μ.ς broadcast p' v'
        → μ.ς broadcast p' v' = .true := by
        intro h1 h2
        have l := bb.BrCorrectBroadcast default; rw [valid_or] at l; simp [denotation] at l
        cases l
        · next h => exact Lemmas.valid_and_TF h2 (h _ _ )
        · next h => rw [h p v] at h1; contradiction

theorem echo_byzantine : μ.ς echo p v = .byzantine → μ.ς echo p v' = .byzantine := by
        intro h1
        have l := bb.BrCorrectEcho p; rw [valid_forall] at l
        specialize l v'; simp only [substSimp, valid_or] at l
        simp [denotation] at l
        cases l
        · next h => specialize h v; rw [h1] at h; simp at h
        · next h => exact h v'

end Lemmas

namespace Lemma_4_2_7

variable
  {V P : Type}
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  [Fintype V]
  [DecidableEq V]
  {μ : Model BBSig P V}
  [bb : ThyBB μ]
  {v : V}

theorem t2 : ⊨[μ] (◇ₑ [broadcast, .val v]ₑ →ₑ □ₑ [echo, .val v]ₑ) := by
  intro p0; rw [Lemmas.valid_impl]; simp [denotation]; intro p h p'
  have i := bb.BrEcho! p'; have i' := i; simp [denotation] at i'; specialize i' v
  simp [Lemmas.le_or] at i'; apply Decidable.or_iff_not_imp_left.mp at i'; simp at i'
  specialize i' p h; obtain ⟨v', e⟩ := i'
  rw [Lemmas.byzantine_le_cases] at e; cases e
  · next g => have e : Model.ς μ echo p' v = .byzantine:= Lemmas.echo_byzantine g; rw [e]
  · next g =>
      have ⟨⟨_, unV, unVp, _⟩, i⟩ := Lemmas.when_broadcast h
      simp [denotation] at unVp; obtain ⟨x1, x2⟩ := unVp
      have e2 := Lemmas.valid_forall.mp (bb.BrEcho? p') v'; simp only [substSimp, Lemmas.valid_impl] at e2; simp [denotation] at e2
      specialize e2 g; obtain ⟨e2, e2p⟩ := e2
      have := i (Lemmas.broadcast_true h e2p)
      subst_vars; rw [g]; decide

theorem t1 : ⊨[μ] (◇ₑ [broadcast, .val v]ₑ →ₑ [echo, .val v]ₑ) := by
  intro p; rw [Lemmas.valid_impl]; intro h
  have h1 : p ⊨[μ] (◇ₑ [broadcast, .val v]ₑ →ₑ □ₑ [echo, .val v]ₑ) := t2 p
  rw [Lemmas.valid_impl] at h1;
  specialize h1 h; apply valid_iff_everywhere.mpr at h1; exact h1 p

theorem t3 : ⊨[μ] (⊡ₑ [echo, .val v]ₑ →ₑ □ₑ [ready, .val v]ₑ) := by
  intro p; rw [Lemmas.valid_impl]; intro h; simp only at h
  apply valid_iff_everywhere.mp; intro p'
  have b := Lemmas.valid_forall.mp (bb.BrReady! p') v
  simp only [substSimp, substAt] at b; rw [Lemmas.substAt_bound] at b
  apply Lemmas.valid_impl.mp b; simpa only [den_quorum_global p' p]

theorem t4 : ⊨[μ] (⊡ₑ [ready, .val v]ₑ →ₑ □ₑ [deliver, .val v]ₑ) := by
  intro p; rw [Lemmas.valid_impl]; intro h; simp only at h
  apply valid_iff_everywhere.mp; intro p'
  have b := Lemmas.valid_forall.mp (bb.BrDeliver! p') v
  simp only [substSimp] at b; rw [Lemmas.substAt_bound] at b
  apply Lemmas.valid_impl.mp b; simpa only [den_quorum_global p' p]

end Lemma_4_2_7

namespace Lemma_4_2_9

variable
  {V P : Type}
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  [Fintype V]
  [DecidableEq V]
  {μ : Model BBSig P V}
  [bb : ThyBB μ]
  {v : V}

theorem t1 (h : ⊨[μ] □ₑ [echo, .val v]ₑ) : ⊨[μ] Tₑ (⊡ₑ [echo, .val v]ₑ) := by
  intro p
  have b := Lemmas.valid_forall.mp (bb.BrCorrect p) v
  simp only [substSimp] at b; replace b := Lemmas.valid_and.mp b |>.2
  rw [TF_all] at b
  simp [denotation] at b; obtain ⟨b1, b2, b3⟩ := b
  simp [denotation]; refine ⟨b1, b2, ?_⟩; intro x xb1
  have i := b3 x xb1 v; specialize h x; simp [denotation] at h
  exact Lemmas.valid_and_TF (h x) i

theorem t2 (h : ⊨[μ] □ₑ [ready, .val v]ₑ) : ⊨[μ] Tₑ (⊡ₑ [ready, .val v]ₑ) := by
  intro p
  have b := Lemmas.valid_forall.mp (bb.BrCorrect p) v
  simp only [substSimp] at b; replace b := Lemmas.valid_and.mp b |>.1
  rw [TF_all] at b
  simp [denotation] at b; obtain ⟨b1, b2, b3⟩ := b
  simp [denotation]; refine ⟨b1, b2, ?_⟩; intro x xb1
  have i := b3 x xb1 v; specialize h x; simp [denotation] at h
  exact Lemmas.valid_and_TF (h x) i

end Lemma_4_2_9

namespace Proposition_4_2_10

variable
  {V P : Type}
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  [Fintype V]
  [DecidableEq V]
  {μ : Model BBSig P V}
  [bb : ThyBB μ]
  {v : V}

theorem t : ⊨[μ] (◇ₑ [broadcast, .val v]ₑ →ₑ □ₑ [deliver, .val v]ₑ) := by
  intro p; rw [Lemmas.valid_impl]; intro h
  have h1 : ∀ p', ⟦◇ₑ [broadcast, .val v]ₑ⟧ᵈ μ p' = .true := by
    intro p'; rw [den_somewhere_global p p'] at h; rw [h]
  have h2 : ⊨[μ] □ₑ [echo, .val v]ₑ := by
    intro p'; apply Lemmas.valid_impl.mp (Lemma_4_2_7.t2 p') (h1 p')
  have h3 : ⊨[μ] Tₑ (⊡ₑ [echo, .val v]ₑ) := Lemma_4_2_9.t1 h2
  have h3' : ∀ p, ⟦⊡ₑ [echo, .val v]ₑ⟧ᵈ μ p = .true := by
    intro p; simpa using h3 p
  have h4 : ⊨[μ] □ₑ [ready, .val v]ₑ := by
    intro p'; exact Lemmas.valid_impl.mp (Lemma_4_2_7.t3 p') (h3' p')
  have h4 : ⊨[μ] Tₑ (⊡ₑ [ready, .val v]ₑ) := Lemma_4_2_9.t2 h4
  have h5 : ⊨[μ] □ₑ [deliver, .val v]ₑ := by
    intro p'; exact Lemmas.valid_impl.mp (Lemma_4_2_7.t4 p') (by simpa using h4 p')
  exact h5 p

end Proposition_4_2_10

namespace Lemma_4_2_11

variable
  {V P : Type}
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  [Fintype V]
  [DecidableEq V]
  {μ : Model BBSig P V}
  [twined : Twined3 μ.S]
  [bb : ThyBB μ]
  {v v' : V}
  {tag : BBSig}

omit bb in
theorem t1_aux {p} {s : BBSig}
  (h1 : p ⊨[μ] ⊡ₑ [s, Term.val v]ₑ)
  (h2 : p ⊨[μ] ⊡ₑ TF[s]ₑ)
  : p ⊨[μ] Tₑ (⟐ₑ [s, Term.val v]ₑ) := by
  rw [valid_pred] at h1 h2; simp only [Lemmas.denotation_quorum] at h1 h2
  have r := Theorem_2_4_4.t2' (Lemmas.le_and.mpr ⟨h1,h2⟩)
  simp at r; simp [denotation]; intro x xm
  have ⟨_, y2, y3⟩ := r _ xm; simp [denotation, Lemmas.le_and] at y3; obtain ⟨y3, y3'⟩ := y3
  refine ⟨_, y2, ?_⟩; refine Lemmas.valid_and_TF y3 (y3' v)

theorem t1 : (⊨[μ] ⊡ₑ [ready, .val v]ₑ) → ⊨[μ] Tₑ (⟐ₑ [ready, .val v]ₑ) := by
  intro h p; specialize h p
  have b := Lemmas.valid_forall.mp (bb.BrCorrect p) v; simp only [substSimp, Lemmas.valid_and] at b
  exact t1_aux h b.1

theorem t2 (h1 : ⊨[μ] (⊡ₑ [echo, .val v]ₑ ∧ₑ ⊡ₑ [echo, .val v']ₑ))
  : ⊨[μ] (Tₑ (◇ₑ ([echo, .val v]ₑ ∧ₑ [echo, .val v']ₑ))) := by
  intro p; specialize h1 p
  have h2 := Lemmas.valid_forall.mp (bb.BrCorrect p) v; simp only [substSimp, Lemmas.valid_and] at h2
  replace h2 := h2.2; simp [denotation]
  simp [denotation] at h1 h2; simp [Lemmas.le_and] at h1
  obtain ⟨⟨s1, s12, s13⟩, s2, s3, s4⟩ := h1; obtain ⟨r1, r2, r3⟩ := h2
  have t := twined.twined s12 s3 r2; simp [Open1] at t; obtain ⟨t1, ⟨t2, t3⟩⟩ := t
  exists t2; simp [Lemmas.and_true]
  obtain ⟨m1, m2⟩ := Finset.mem_inter.mp t3; obtain ⟨m2, m3⟩ := Finset.mem_inter.mp m2;
  constructor
  apply Lemmas.valid_and_TF; apply s13; assumption; apply r3; assumption;
  apply Lemmas.valid_and_TF; apply s4 t2; assumption; apply r3; assumption

theorem t2' (h1 : ⊨[μ] (⊡ₑ [echo, .val v]ₑ)) : ⊨[μ] (Tₑ (◇ₑ [echo, .val v]ₑ)) := by
  intro p; specialize h1 p
  have h2 := Lemmas.valid_forall.mp (bb.BrCorrect p) v; simp only [substSimp, Lemmas.valid_and] at h2
  replace h2 := h2.2; simp [denotation]
  simp [denotation] at h1 h2
  obtain ⟨s1, s12, s13⟩ := h1; obtain ⟨r1, r2, r3⟩ := h2
  have t := twined.twined s12 s12 r2; simp [Open1] at t; obtain ⟨t1, ⟨t2, t3⟩⟩ := t
  exists t2; obtain ⟨m1, m2⟩ := Finset.mem_inter.mp t3
  apply Lemmas.valid_and_TF; apply s13; assumption; apply r3; assumption;

theorem t3 (h1 : ⊨[μ] (⊡ₑ [ready, .val v]ₑ ∧ₑ ⊡ₑ [ready, .val v']ₑ))
  : ⊨[μ] (Tₑ (◇ₑ ([ready, .val v]ₑ ∧ₑ [ready, .val v']ₑ))) := by
  intro p; specialize h1 p
  have h2 := Lemmas.valid_forall.mp (bb.BrCorrect p) v; simp only [substSimp, Lemmas.valid_and] at h2
  replace h2 := h2.1; simp [denotation]
  simp [denotation] at h1 h2; simp [Lemmas.le_and] at h1
  obtain ⟨⟨s1, s12, s13⟩, s2, s3, s4⟩ := h1; obtain ⟨r1, r2, r3⟩ := h2
  have t := twined.twined s12 s3 r2; simp [Open1] at t; obtain ⟨t1, ⟨t2, t3⟩⟩ := t
  exists t2; simp [Lemmas.and_true]
  obtain ⟨m1, m2⟩ := Finset.mem_inter.mp t3; obtain ⟨m2, m3⟩ := Finset.mem_inter.mp m2;
  constructor
  apply Lemmas.valid_and_TF; apply s13; assumption; apply r3; assumption;
  apply Lemmas.valid_and_TF; apply s4 t2; assumption; apply r3; assumption

end Lemma_4_2_11

namespace Proposition_4_2_12

variable
  {P V : Type}
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  [Fintype V]
  [DecidableEq V]
  {μ : Model BBSig P V}
  [bb : ThyBB μ]
  [twined : Twined3 μ.S]
  {v : V}

theorem t : ⊨[μ] ∃₀₁ₑ (◇ₑ [deliver]ₑ) := by
  intro p;
  simp only [valid_pred, Lemmas.denotation_exists_affine, substSimp, Lemmas.byzantine_le_affine_implies_eq]
  intro v1 v2 h1 h2; simp [denotation] at h1 h2; obtain ⟨u1, u2⟩ := h1; obtain ⟨w1, w2⟩ := h2
  have d1 := bb.BrDeliver?' u2; have d2 := bb.BrDeliver?' w2
  have mke {p'} {v} (x : Model.ς μ ready p' v = .true) : ⊨[μ] (⊡ₑ [echo, .val v]ₑ) := by
    intro p2;
    have h := Lemmas.valid_forall.mp (bb.BrReady? p') v
    simp only [substSimp] at h; simp only [Lemmas.valid_impl] at h
    rw [Lemmas.substAt_bound] at h; simp only [denotation] at h
    exact quorum_global'.mp (h x) p2
  have hr : ⊨[μ] (Tₑ (◇ₑ ([ready, .val v1]ₑ ∧ₑ [ready, .val v2]ₑ))) := by
    apply Lemma_4_2_11.t3; intro p
    apply Lemmas.valid_and.mpr
    exact ⟨d1 p, d2 p⟩
  have exvready : ∃ p', (Model.ς μ ready p' v1 = Three.true) ∧ Model.ς μ ready p' v2 = Three.true := by
    specialize hr default
    simpa [denotation, Lemmas.and_true] using hr
  obtain ⟨r, r1, r2⟩ := exvready
  have he : ⊨[μ] (Tₑ (◇ₑ ([echo, .val v1]ₑ ∧ₑ [echo, .val v2]ₑ))) := by
    apply Lemma_4_2_11.t2; intro p
    apply Lemmas.valid_and.mpr
    constructor; apply mke r1; apply mke r2
  specialize he default; simp [denotation, Lemmas.and_true] at he; obtain ⟨y, y1, y2⟩ := he
  have z := bb.BrEcho01 y
  rw [valid_pred, Lemmas.denotation_exists_affine] at z; simp only at z
  conv at z => right; right; ext v; simp [Lemmas.substAt_atom, Lemmas.substAt_bound, denotation]
  apply Lemmas.byzantine_le_affine_implies_eq.mp z y1 y2

end Proposition_4_2_12

namespace Proposition_4_2_13

variable
  {P V : Type}
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  [Fintype V]
  [DecidableEq V]
  {μ : Model BBSig P V}
  [bb : ThyBB μ]
  [twined : Twined3 μ.S]
  {v : V}

theorem t : ⊨[μ] ([deliver, .val v]ₑ →ₑ ◇ₑ [broadcast, .val v]ₑ) := by
  intro p; rw [Lemmas.valid_impl]; simp [denotation]; intro h
  have l := bb.BrDeliver?' (by simpa [denotation] using h)
  have s1 : ⊨[μ] Tₑ (⟐ₑ [ready, Term.val v]ₑ) := Lemma_4_2_11.t1 l
  have s2 : ⊨[μ] Tₑ (◇ₑ [ready, Term.val v]ₑ) := by
    intro _; simp [denotation]
    specialize s1 default; simp [denotation] at s1; specialize s1 Finset.univ univ_in_Open1
    simpa using s1
  specialize s2 default; simp [denotation] at s2; obtain ⟨x1, x2⟩ := s2
  have t : ⊨[μ] ⊡ₑ [echo, .val v]ₑ := by
    have t' := Lemmas.valid_forall.mp (bb.BrReady? x1) v; simp only [substSimp, Lemmas.valid_impl] at t'
    specialize t' (by simpa [denotation] using x2)
    exact quorum_global'.mp t'
  have t2 : ⊨[μ] Tₑ (◇ₑ [echo, .val v]ₑ) := Lemma_4_2_11.t2' t
  specialize t2 default; simp [denotation] at t2; obtain ⟨y1, y2⟩ := t2
  have r := Lemma_4_2_11.t1 l default; simp [denotation] at r
  have b := Lemmas.valid_forall.mp (bb.BrEcho? y1) v; simp only [substSimp, Lemmas.valid_impl] at b
  simp [denotation] at b; exact b y2

end Proposition_4_2_13

namespace Proposition_4_2_14

variable
  {P V : Type}
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  [Fintype V]
  [DecidableEq V]
  {μ : Model BBSig P V}
  [bb : ThyBB μ]
  [twined : Twined3 μ.S]
  {v : V}

theorem t : ⊨[μ] (◇ₑ [deliver, .val v]ₑ →ₑ □ₑ [deliver, .val v]ₑ) := by
  intro _; simp only [Lemmas.valid_impl]; simp [denotation]
  intro p1 h p2
  have r := Lemma_4_2_11.t1 (bb.BrDeliver?' h)
  apply bb.BrDeliver!'; apply Lemma_4_2_9.t2
  have rr := bb.BrReady!!' r
  intro _; simp [denotation]; intro p3
  specialize rr p3; simpa [denotation] using rr

end Proposition_4_2_14
