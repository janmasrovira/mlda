import mlda.Base
import mlda.Section2
import mlda.Section3
import Mathlib.Tactic.Attr.Register

/-!
# Section 5: Crusader Agreement

This file formalises the Crusader Agreement consensus protocol:

- **Value domain** (`Val`): three values `0`, `1`, `½`.
- **Signature** (`Sig`): input, echo₁, echo₂, output.
- **Axioms** (`Thy`): axioms for Crusader Agreement
- **Correctness proofs**: weak agreement (`Proposition_5_3_3.t`), validity (`Proposition_5_3_6.t1`, `Proposition_5_3_6.t3`), liveness (`Proposition_5_3_11.t`)
-/

#eval IO.println "Checking definitions and proofs in Section 5..."

open Three
open scoped Three.Atom
open scoped Three.Function
open scoped FinSemitopology
open FinSemitopology
open scoped Definition_3_1_1
open Definition_3_1_1
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

section Definition_5_1_2

inductive Val where
  | v0
  | vhalf
  | v1
  deriving DecidableEq, FinEnum, Ord

namespace Val

scoped notation " 𝟢 " => Val.v0
scoped notation " ½ " => Val.vhalf
scoped notation " 𝟣 " => Val.v1

instance : Max Val where
  max a b := match a, b with
   | 𝟣, _  => 𝟣
   | _, 𝟣  => 𝟣
   | ½, _  => ½
   | _, ½  => ½
   | _, _ => 𝟢

instance : Min Val where
  min a b := match a, b with
   | 𝟢, _  => 𝟢
   | _, 𝟢  => 𝟢
   | ½, _  => ½
   | _, ½  => ½
   | _, _ => 𝟣

instance : LinearOrder Val := by
  let toFin : Val → Fin 3
    | 𝟢 => 0
    | ½ => 1
    | 𝟣 => 2
  apply LinearOrder.liftWithOrd toFin
  intro x y p; cases x <;> cases y <;> cases p <;> rfl
  repeat (intro x y; cases x <;> cases y <;> rfl)

class inductive NotHalf : Val → Prop
  | v0 : NotHalf 𝟢
  | v1 : NotHalf 𝟣

scoped notation "≠½ " => NotHalf

instance : ≠½ 𝟢 := .v0
instance : ≠½ 𝟣 := .v1

theorem NotHalf_iff_neq {v} : NotHalf v ↔ v ≠ ½ := by
  cases v <;> simp
  · exact .v0
  · intro c; cases c
  · exact .v1

abbrev complement : Val → Val
  | 𝟢 => 𝟣
  | 𝟣 => 𝟢
  | ½ => ½

scoped notation "~" => complement

@[simp] theorem complement_v0 : ~ 𝟢 = 𝟣 := rfl
@[simp] theorem complement_v1 : ~ 𝟣 = 𝟢 := rfl
@[simp] theorem complement_half : ~ ½ = ½ := rfl
@[simp] theorem complement_complement {v : Val} : ~ (~ v) = v := by cases v <;> rfl

end Val

open scoped Val
open Val

inductive Sig where
  | input
  | echo₁
  | echo₂
  | output

export Sig (input echo₁ echo₂ output)

class Thy (μ : Model Sig P Val) where
  CaEcho1? : ⊨[μ] ∀ₑ ([echo₁]ₑ ⇀ₑ ◇ₑ [input]ₑ)
  CaEcho2? : ⊨[μ] ∀ₑ ([echo₂]ₑ →ₑ ⊡ₑ [echo₁]ₑ)
  CaOutput? : ⊨[μ] ([output, 𝟢]ₑ →ₑ ⊡ₑ [echo₂, 𝟢]ₑ) ∧ₑ
                     ([output, 𝟣]ₑ →ₑ ⊡ₑ [echo₂, 𝟣]ₑ)
  CaOutput'? : ⊨[μ] [output, ½]ₑ →ₑ (⊡ₑ [echo₁, 𝟢]ₑ ∧ₑ ⊡ₑ [echo₁, 𝟣]ₑ)
  CaCorrect : ⊨[μ] ⊡ₑ TF[input, echo₁, echo₂, output]ₑ
  CaCorrect' (s : Sig) : ⊨[μ] TF[s]ₑ ∨ₑ B[s]ₑ
  CaInput : ⊨[μ] ([input, 𝟢]ₑ ⊕ₑ [input, 𝟣]ₑ) ∧ₑ (¬ₑ [input, ½]ₑ)
  CaEcho2Affine : ⊨[μ] ∃₀₁ₑ [echo₂]ₑ -- axiom called CaEcho2_01 in the paper
  CaEcho1! : ⊨[μ] ∀ₑ (([input]ₑ ∨ₑ ⟐ₑ [echo₁]ₑ) →ₑ [echo₁]ₑ)
  CaEcho2! : ⊨[μ] (∃⁎ₑ (⊡ₑ [echo₁]ₑ)) →ₑ ∃⁎ₑ [echo₂]ₑ
  CaOutput! : ⊨[μ] ∀ₑ (⊡ₑ [echo₂]ₑ →ₑ [output]ₑ)
  CaOutput'! : ⊨[μ] (⊡ₑ [echo₁, 𝟢]ₑ ∧ₑ ⊡ₑ [echo₁, 𝟣]ₑ) →ₑ [output, ½]ₑ

end Definition_5_1_2

open scoped Val
open Val

namespace Thy

variable
  {μ : Model Sig P Val}
  [ca : Thy μ]
  {p : P}
  {v v' : Val}

theorem CaCorrect1 (s : Sig) : ⊨[μ] ⊡ₑ TF[s]ₑ := by
  have c := ca.CaCorrect default
  intro _
  simp [TF_all_many, TF_conj, denotation] at c ⊢
  obtain ⟨c1, c2, c3⟩ := c; refine ⟨_, c2, ?_⟩
  intro x1 x2 v; specialize c3 x1 x2 v
  cases s <;> grind [Lemmas.le_and]

theorem CaCorrect2 (s1 s2 : Sig) : ⊨[μ] ⊡ₑ (TF[s1]ₑ ∧ₑ TF[s2]ₑ) := by
  have c := ca.CaCorrect default
  intro _
  simp [TF_all_many, TF_conj, denotation] at c ⊢
  obtain ⟨c1, c2, c3⟩ := c; refine ⟨_, c2, ?_⟩
  intro x1 x2; specialize c3 x1 x2
  simp [Lemmas.or_le];
  constructor <;> intro v <;> specialize c3 v <;> cases s1 <;> cases s2 <;> grind [Lemmas.le_and]

theorem CaOutput'?_simp : (μ.ς output p ½ = 𝐭)
  → ((⊨[μ] ⊡ₑ [echo₁, 𝟢]ₑ) ∧ ⊨[μ] ⊡ₑ [echo₁, 𝟣]ₑ) := by
  intro h; have b := CaOutput'? (μ := μ) p
  simp only [Lemmas.valid_impl] at b; specialize b (by simpa [denotation] using h)
  have t := Lemmas.valid_and.mp b
  constructor; exact quorum_global'.mp t.1; exact quorum_global'.mp t.2

theorem CaEcho1!_simp_echo : (⊨[μ] Tₑ (⟐ₑ [echo₁, v]ₑ)) → ⊨[μ] [echo₁, v]ₑ := by
  intro h p; have b := ca.CaEcho1! p
  apply Lemmas.valid_forall_specialize v at b
  simp only [substSimp, Lemmas.valid_impl, Lemmas.denotation_or] at b
  apply b; rw [Lemmas.or_true]; right; simpa using h p

theorem CaEcho2!_simp (h : ⊨ (⊡(μ.S) (fun p => T (μ.ς echo₁ p v)))) : ∀p', ∃ v', ⊨ (μ.ς echo₂ p' v') := by
  intro p'; have b := ca.CaEcho2! p';
  simp only [Lemmas.valid_impl] at b; simp [denotation] at b h
  obtain ⟨h1, h2, h3⟩ := h; specialize b v; apply b h1 h2 h3

theorem CaCorrect_simp (s : Sig) : ⊨ (⊡(μ.S) (fun p => TF (μ.ς s p v))) := by
  have b := ca.CaCorrect1 s default
  simp [denotation] at b
  simp; grind only

theorem CaOutput?_simp [n : ≠½ v] : μ.ς output p v = 𝐭 → ⊨[μ] ⊡ₑ [echo₂, v]ₑ := by
  cases n
  · intro h;
    have c1 := ca.CaOutput?; specialize c1 p; rw [Lemmas.valid_and] at c1; obtain ⟨c0, c1⟩ := c1
    rw [Lemmas.valid_impl] at c0 c1; apply quorum_global'.mp; apply c0; simp [denotation]; exact h
  · intro h;
    have c1 := ca.CaOutput?; specialize c1 p; rw [Lemmas.valid_and] at c1; obtain ⟨c0, c1⟩ := c1
    rw [Lemmas.valid_impl] at c0 c1; apply quorum_global'.mp; apply c1; simp [denotation]; exact h

theorem CaEcho1?_simp : μ.ς echo₁ p v = 𝐭 → ∃ p, μ.ς input p v = 𝐭 := by
  have b := ca.CaEcho1? p; simp only [Lemmas.valid_forall, substSimp] at b; specialize b v
  simp only [Lemmas.valid_impl] at b; simp [denotation] at b
  assumption

theorem CaEcho2?_simp : μ.ς echo₂ p v = 𝐭 → ⊨[μ] ⊡ₑ [echo₁, v]ₑ := by
  intro h
  have b := ca.CaEcho2? p; simp only [Lemmas.valid_forall, substSimp] at b; specialize b v
  simp only [Lemmas.valid_impl] at b; specialize b (by simpa [denotation] using h)
  apply quorum_global'.mp b

theorem CaCorrect'_byzantine {s : Sig} (h : μ.ς s p v = 𝐛) : ∀ {v'}, μ.ς s p v' = 𝐛 := by
  intro v'; have b := ca.CaCorrect' s p; simp only [Lemmas.valid_or] at b; cases b
  · next g => simp [denotation] at g; specialize g v; rw [h] at g; contradiction
  · next g => simp [denotation] at g; exact g v'

theorem CaCorrect'_true {s : Sig} (h : μ.ς s p v ≠ 𝐛) : ∀ {v'}, 𝐛 ≤ μ.ς s p v' → μ.ς s p v' = 𝐭 := by
  intro v' w; have b := ca.CaCorrect' s p; simp only [Lemmas.valid_or] at b; cases b
  · next g => simp [denotation] at g; specialize g v'; exact Lemmas.valid_and_TF w g
  · next g => simp [denotation] at g; rw [g v] at h; contradiction

theorem CaCorrect'_false {s : Sig} (h : μ.ς s p v ≠ 𝐛) : ∀ {v'}, μ.ς s p v' ≤ 𝐛 → μ.ς s p v' = 𝐟 := by
  intro v' w; have b := ca.CaCorrect' s p; simp only [Lemmas.valid_or] at b; cases b
  · next g => simp [denotation] at g; specialize g v';
              simp [Lemmas.byzantine_le_TF] at g
              simp [Lemmas.le_byzantine] at w; cases w; assumption; contradiction
  · next g => simp [denotation] at g; rw [g v] at h; contradiction

theorem CaInput_half : μ.ς input p ½ ≤ 𝐛 := by
  have b := ca.CaInput p; simp [denotation, Lemmas.le_and] at b; exact b.2

theorem CaInput_1_le (h1 : 𝐛 ≤ μ.ς input p 𝟢) : μ.ς input p 𝟣 ≤ 𝐛 := by
  have b := ca.CaInput p; simp [denotation, Lemmas.le_and] at b; replace b := b.1
  simp [Lemmas.le_or, Lemmas.le_and] at b; cases b
  · next h => exact h.2
  · next h => obtain ⟨h1, h2⟩ := h; have b : μ.ς input p 𝟢 = 𝐛 := by grind
              rw [ca.CaCorrect'_byzantine b]

theorem CaInput_0_1 :
    𝐛 ≤ μ.ς input p 𝟢 ∧ μ.ς input p 𝟣 ≤ 𝐛 ∨
    μ.ς input p 𝟢 ≤ 𝐛 ∧ 𝐛 ≤ μ.ς input p 𝟣 := by
  have b := ca.CaInput p; simp only [Lemmas.valid_and] at b; obtain b := b.1
  simp [denotation, Lemmas.le_or, Lemmas.le_and] at b
  exact b

theorem CaInput_0_le (h1 : 𝐛 ≤ μ.ς input p 𝟣) : μ.ς input p 𝟢 ≤ 𝐛 := by
  have b := ca.CaInput p; simp [denotation, Lemmas.le_and] at b; replace b := b.1
  simp [Lemmas.le_or, Lemmas.le_and] at b; cases b
  · next h => obtain ⟨h1, h2⟩ := h; have b : μ.ς input p 𝟣 = 𝐛 := by grind
              rw [ca.CaCorrect'_byzantine b]
  · next h => exact h.1

theorem CaInput_le_0 (h1 : μ.ς input p 𝟣 ≤ 𝐛) : 𝐛 ≤ μ.ς input p 𝟢 := by
  have b := ca.CaInput p; simp [denotation, Lemmas.le_and] at b; replace b := b.1
  simp [Lemmas.le_or, Lemmas.le_and] at b; cases b
  · next h => exact h.1
  · next h => obtain ⟨h1, h2⟩ := h; have b : μ.ς input p 𝟣 = 𝐛 := by grind
              rw [ca.CaCorrect'_byzantine b]

theorem CaInput_le_1 (h1 : μ.ς input p 𝟢 ≤ 𝐛) : 𝐛 ≤ μ.ς input p 𝟣 := by
  have b := ca.CaInput p; simp [denotation, Lemmas.le_and] at b; replace b := b.1
  simp [Lemmas.le_or, Lemmas.le_and] at b; cases b
  · next h => obtain ⟨h1, h2⟩ := h; have b : μ.ς input p 𝟢 = 𝐛 := by grind
              rw [ca.CaCorrect'_byzantine b]
  · next h => exact h.2

theorem CaInput_v_le {v} [n : ≠½ v] (h1 : 𝐛 ≤ μ.ς input p (~ v)) : μ.ς input p v ≤ 𝐛 := by
  cases n
  · exact CaInput_0_le h1
  · exact CaInput_1_le h1

theorem CaInput_le_v {v} [n : ≠½ v] (h1 : μ.ς input p (~ v) ≤ 𝐛) : 𝐛 ≤ μ.ς input p v := by
  cases n
  · exact CaInput_le_0 h1
  · exact CaInput_le_1 h1

end Thy

namespace Proposition_5_3_3

variable
  (μ : Model Sig P Val)
  [ca : Thy μ]
  [twined : Twined3 μ.S]
  {v v' : Val}

theorem t' [≠½ v] [≠½ v'] : ⊨[μ] ((◇ₑ [output, v]ₑ ∧ₑ ◇ₑ [output, v']ₑ) ⇀ₑ (.val v =ₑ .val v')) := by
  intro p; simp only [Lemmas.valid_impl]; intro h
  simp [denotation] at h; obtain ⟨⟨h1, h2⟩, ⟨g1, g2⟩⟩ := h
  have q1 : ⊨[μ] ⊡ₑ [echo₂, v]ₑ := by apply ca.CaOutput?_simp; assumption
  have q2 : ⊨[μ] ⊡ₑ [echo₂, v']ₑ := by apply ca.CaOutput?_simp; assumption
  have q1' : ⊨[μ] ⟐ₑ ([echo₂, v]ₑ ∧ₑ [echo₂, v']ₑ) := by
    intro _; simp only [valid_pred, Lemmas.denotation_contraquorum, denotation]
    apply Theorem_2_4_5.t2'; rw [Lemmas.le_and]; constructor
    · simpa [denotation] using q1 p
    · simpa [denotation] using q2 p
  have c2 : ⊨[μ] (⊡ₑ TF[echo₂]ₑ) := ca.CaCorrect1 echo₂
  have h3 : ⊨[μ] (Tₑ (◇ₑ ([echo₂, v]ₑ ∧ₑ [echo₂, v']ₑ))):= by
    intro _; simp [denotation];
    have l : ⊨ (T (◇ (⟦[echo₂, v]ₑ ∧ₑ [echo₂, v']ₑ⟧ᵈ μ))) := by
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

theorem t : ⊨[μ] (◇ₑ [output, v]ₑ ∧ₑ ◇ₑ [output, v']ₑ) ⇀ₑ
  ((.val v =ₑ .val v') ∨ₑ (.val v =ₑ .val ½) ∨ₑ (.val v' =ₑ .val ½)):= by
  intro p; simp only [Lemmas.valid_impl]; intro h; simp [denotation, Lemmas.or_true]
  by_cases v = ½
  · grind
  · by_cases v' = ½
    · grind
    · next h1 h2 =>
      have := NotHalf_iff_neq.mpr h1; have := NotHalf_iff_neq.mpr h2
      have b := Lemmas.valid_impl.mp (t' (μ := μ) (v := v) (v' := v') p) h
      simp [denotation] at b; grind

end Proposition_5_3_3

namespace Lemma_5_3_5

variable
  {μ : Model Sig P Val}
  [ca : Thy μ]
  {v v' : Val}
  {p : P}

theorem t1 : p ⊨[μ] ¬ₑ [input, ½]ₑ := by
  simp [denotation]; exact ca.CaInput_half

theorem t2 [i : ≠½ v] : (p ⊨[μ] [input, v]ₑ) ↔ p ⊨[μ] ¬ₑ [input, (~ v)]ₑ := by
  by_cases e : μ.ς input p v = 𝐛
  · simp [denotation, ca.CaCorrect'_byzantine e]
  · simp [denotation]; cases i
    · simp!; constructor
      · exact ca.CaInput_1_le
      · exact ca.CaInput_le_0
    · simp!; constructor
      · exact ca.CaInput_0_le
      · exact ca.CaInput_le_1

theorem t3_aux (o : v ≤ v') (h1 : p ⊨[μ] Tₑ [input, v]ₑ) (h2 : p ⊨[μ] Tₑ [input, v']ₑ) : v = v' := by
  simp [denotation] at h1 h2
  rcases lt_trichotomy v v' with h | h | h
  · exfalso; clear o; cases v <;> cases v' <;> try contradiction
    · have b := t1 (p := p) (μ := μ); simp [denotation, h2] at b
    · have b := t2 (p := p) (μ := μ) (v := 𝟣).mp; simp! [denotation, h1, h2] at b
    · have b := t1 (p := p) (μ := μ); simp [denotation, h1] at b
  · assumption
  · exact absurd h (not_lt.mpr o)

theorem t3 (h1 : p ⊨[μ] Tₑ [input, v]ₑ) (h2 : p ⊨[μ] Tₑ [input, v']ₑ) : v = v' := by
  cases LinearOrder.le_total v v'
  · next h => apply t3_aux (μ := μ) h h1 h2
  · next h => apply Eq.symm; apply t3_aux (μ := μ) h h2 h1

theorem t4 (h1 : p ⊨[μ] □ₑ [input, v]ₑ) (h2 : p ⊨[μ] Tₑ (◇ₑ [input, v']ₑ)) : v = v' := by
  simp [denotation] at h1 h2; obtain ⟨p', h2⟩ := h2; specialize h1 p'
  have t : μ.ς input p' v = 𝐭 := ca.CaCorrect'_true (by intro x; rw [x] at h2; contradiction) h1
  apply t3 (μ := μ)
  · simp [denotation]; exact t
  · simp [denotation]; exact h2

theorem t5 [Twined3 μ.S] : p ⊨[μ] ¬ₑ [echo₂, ½]ₑ := by
  simp [denotation]
  rcases Lemmas.true_or_le_byzantine (a := μ.ς echo₂ p ½) with h | h
  · exfalso
    have q1 : ⊨[μ] ⊡ₑ [echo₁, ½]ₑ := ca.CaEcho2?_simp h
    have q1' : ⊨ (⟐(μ.S) fun p ↦ μ.ς echo₁ p ½) :=
      Theorem_2_4_5.t'' (by simpa [denotation] using q1 p)
    have tf := ca.CaCorrect_simp (v := ½) echo₁
    have q2 := Lemma_2_3_7.c3 tf q1'
    simp at q2; obtain ⟨_, q2'⟩ := q2
    have ⟨p', hp'⟩ := ca.CaEcho1?_simp q2'
    have w := ca.CaInput_half (p := p'); rw [hp'] at w; contradiction
  · exact h

end Lemma_5_3_5

namespace Proposition_5_3_6

variable
  {μ : Model Sig P Val}
  [ca : Thy μ]
  [twined : Twined3 μ.S]
  {v v' : Val}
  {p : P}

omit ca in
theorem quorum_and_TF {s} (h1 : ⊨[μ] ⊡ₑ [s, v]ₑ) (h2 : ⊨[μ] ⊡ₑ (TFₑ [s, v]ₑ)) : ⊨[μ] Tₑ (◇ₑ [s, v]ₑ) := by
  intro p; simp [denotation]; specialize h2 default
  have q : ⊨ (⟐(μ.S) fun p ↦ μ.ς s p v) := Theorem_2_4_5.t'' (by simpa [denotation] using h1 p)
  have b := Lemma_2_3_7.c3 ?_ q; simpa using b
  simpa [denotation] using h2

omit ca in
theorem quorum_and_TF' {s} (h1 : ⊨[μ] ⊡ₑ [s, v]ₑ) (h2 : ⊨[μ] ⊡ₑ TF[s]ₑ) : ⊨[μ] Tₑ (◇ₑ [s, v]ₑ) := by
  apply quorum_and_TF h1
  intro p; specialize h2 default; simp [denotation] at h2 ⊢; grind

theorem t1' [≠½ v] : ⊨[μ] ◇ₑ [output, v]ₑ ⇀ₑ ◇ₑ [input, v]ₑ := by
  intro _; simp only [Lemmas.valid_impl]; simp [denotation]; intro p h
  have q1 : ⊨ (T (◇ (fun p => μ.ς echo₂ p v))) := by
    have b : ⊨[μ] ⊡ₑ [echo₂, v]ₑ := ca.CaOutput?_simp h
    have q : ⊨ (⟐(μ.S) fun p ↦ μ.ς echo₂ p v) := Theorem_2_4_5.t'' (by simpa [denotation] using b p)
    apply Lemma_2_3_7.c3; have b := ca.CaCorrect1 echo₂ p
    simp [denotation] at b; obtain ⟨b1, b2, b3⟩ := b
    simp; refine ⟨_, b2, ?_⟩; intro x; specialize b x; intro a; apply b3
    exact a; exact q
  simp at q1; obtain ⟨q1, q1'⟩ := q1
  have q2 : ⊨ (T (◇ (fun p => μ.ς echo₁ p v))) := by
    have b : ⊨[μ] ⊡ₑ [echo₂, v]ₑ := ca.CaOutput?_simp h
    have qe : ⊨[μ] ⊡ₑ [echo₁, v]ₑ := ca.CaEcho2?_simp q1'
    have q : ⊨ (⟐(μ.S) fun p ↦ μ.ς echo₁ p v) := Theorem_2_4_5.t'' (by simpa [denotation] using qe p)
    apply Lemma_2_3_7.c3
    have b := ca.CaCorrect1 echo₁ p
    simp [denotation] at b; obtain ⟨b1, b2, b3⟩ := b
    simp; refine ⟨_, b2, ?_⟩; intro x; specialize b x; intro a; apply b3
    exact a; exact q
  simp at q2; obtain ⟨q2, q2'⟩ := q2
  apply ca.CaEcho1?_simp q2'

theorem t1 : ⊨[μ] ◇ₑ [output, v]ₑ ⇀ₑ ((◇ₑ [input, v]ₑ) ∨ₑ (.val v =ₑ .val ½)) := by
  intro p; rw [Lemmas.valid_impl]; intro h; rw [Lemmas.valid_T, Lemmas.denotation_or, Lemmas.or_true]
  by_cases v = ½
  · right; simpa [denotation]
  · next n => left; apply NotHalf_iff_neq.mpr at n
              have b := t1' (v := v) (μ := μ) p
              rw [Lemmas.valid_impl] at b; simpa using b h

theorem t2 : ⊨[μ] ◇ₑ [output, ½]ₑ ⇀ₑ (◇ₑ [input, 𝟢]ₑ ∧ₑ ◇ₑ [input, 𝟣]ₑ) := by
  intro p; simp only [Lemmas.valid_impl]; intro h; simp [denotation] at h; obtain ⟨h1, h2⟩ := h
  simp only [Lemmas.valid_T, Lemmas.denotation_and, Lemmas.and_true]
  have e1 := ca.CaOutput'?_simp h2
  have e2 := ca.CaCorrect1 echo₁
  have x1 := quorum_and_TF' e1.1 e2 default;
  have x2 := quorum_and_TF' e1.2 e2 default
  simp [denotation] at x1 x2 ⊢
  obtain ⟨_, x1⟩ := x1
  obtain ⟨_, x2⟩ := x2
  have y1 := ca.CaEcho1?_simp x1
  have y2 := ca.CaEcho1?_simp x2
  exact ⟨y1, y2⟩

theorem t3 (h1 : ⊨[μ] □ₑ [input, v]ₑ) (h2 : ⊨[μ] Tₑ (◇ₑ [output, v']ₑ)) : v = v' := by
  by_cases v' = ½
  · next n =>
    exfalso; subst_vars
    have b := t2 (μ := μ) default; simp only [Lemmas.valid_impl] at b
    specialize b (by simpa using h2 default);
    simp only [Lemmas.valid_T, Lemmas.denotation_and, Lemmas.and_true] at b
    obtain ⟨b1, b2⟩ := b
    have e1 := Lemma_5_3_5.t4 (h1 default) (by simpa using b1)
    have e2 := Lemma_5_3_5.t4 (h1 default) (by simpa using b2)
    subst_vars; contradiction
  · next n =>
    have := NotHalf_iff_neq.mpr n
    have b := t1' (v := v') (μ := μ) default; simp only [Lemmas.valid_impl] at b
    specialize b (by simpa using h2 default)
    exact Lemma_5_3_5.t4 (h1 default) (by simpa using b)

end Proposition_5_3_6

namespace Lemma_5_3_8

variable
  {μ : Model Sig P Val}
  [ca : Thy μ]
  {v v' : Val}
  {p : P}

theorem t1 [twined : Twined3 μ.S] (h : ⊨[μ] ⊡ₑ [echo₁, v]ₑ) : ⊨[μ] Tₑ (⟐ₑ [echo₁, v]ₑ) := by
  intro p; have c := ca.CaCorrect_simp (v := v) echo₁
  specialize h p; rw [Lemmas.valid_quorum] at h
  have q := Theorem_2_4_5.t2 (Lemmas.le_and.mpr ⟨c, h⟩)
  simp [denotation] at q ⊢
  intro x xm; specialize q x xm; obtain ⟨q1, q2, q3⟩ := q
  refine ⟨_, q2, ?_⟩; rw [Lemmas.le_and] at q3
  exact Lemmas.valid_and_TF q3.2 q3.1

theorem t2 (h : ⊨[μ] Tₑ (⟐ₑ [echo₁, v]ₑ)) : ⊨[μ] □ₑ [echo₁, v]ₑ := by
  intro _; simp [denotation]; intro p
  simpa [denotation] using ca.CaEcho1!_simp_echo h p

theorem t3 (h : ⊨[μ] □ₑ [echo₁, v]ₑ) : ⊨[μ] Tₑ (⊡ₑ [echo₁, v]ₑ) := by
  have b := ca.CaCorrect1 echo₁ default; simp [denotation] at b;
  intro _; simp only [valid_pred, Lemmas.denotation_T, Lemmas.denotation_quorum]
  apply Lemma_2_3_6.t3; simp only [Lemmas.le_and]; constructor
  simp; intro p; specialize h default; simp [denotation] at h; simpa [denotation] using h p
  simp [denotation]; grind

theorem t [twined : Twined3 μ.S] (h : ⊨[μ] ⊡ₑ [echo₁, v]ₑ) : ⊨[μ] Tₑ (⊡ₑ [echo₁, v]ₑ) := (t3 ∘ t2 ∘ t1) h

end Lemma_5_3_8

namespace Corollary_5_3_9

variable
  {μ : Model Sig P Val}
  [ca : Thy μ]
  {v : Val}

theorem t [twined : Twined3 μ.S] : ⊨[μ] [echo₂, v]ₑ ⇀ₑ ⊡ₑ [echo₁, v]ₑ := by
  intro p; simp only [Lemmas.valid_impl]; intro h
  apply Lemma_5_3_8.t; intro p';
  apply ca.CaEcho2?_simp (by simpa [denotation] using h)

end Corollary_5_3_9

namespace Corollary_5_3_10

variable
  {μ : Model Sig P Val}
  [ca : Thy μ]
  [twined : Twined3 μ.S]
  {v : Val}

theorem t1 : ⊨[μ] Tₑ (⟐ₑ ([input, 𝟢]ₑ ∧ₑ TF[echo₁]ₑ)) ∨ₑ Tₑ (⟐ₑ ([input, 𝟣]ₑ ∧ₑ TF[echo₁]ₑ)) := by
  have s1 : ⊨[μ] □ₑ ([input, 𝟢]ₑ ∨ₑ [input, 𝟣]ₑ) ∧ₑ ⊡ₑ (TF[echo₁]ₑ ∧ₑ TF[input]ₑ) := by
    intro _; simp only [Lemmas.valid_and]; constructor
    · simp [denotation, Lemmas.le_or]; intro p; grind [ca.CaInput_0_1 (p := p)]
    · exact ca.CaCorrect2 echo₁ input _
  have s2 : ⊨[μ] ⊡ₑ (([input, 𝟢]ₑ ∨ₑ [input, 𝟣]ₑ) ∧ₑ (TF[echo₁]ₑ ∧ₑ TF[input]ₑ)) := by
    intro _
    simp only [valid_pred, Lemmas.denotation_quorum, Lemmas.denotation_and]
    have h := s1 default
    simp only [valid_pred, Lemmas.denotation_and, Lemmas.denotation_everywhere,
        Lemmas.denotation_quorum] at h
    exact Lemma_2_3_6.t2 _ _ h
  have s3 : ⊨[μ] ⊡ₑ (([input, 𝟢]ₑ ∧ₑ (TF[echo₁]ₑ ∧ₑ TF[input]ₑ)) ∨ₑ ([input, 𝟣]ₑ ∧ₑ (TF[echo₁]ₑ ∧ₑ TF[input]ₑ))) := by
    intro p; have h := s2 p
    simp only [valid_pred, Lemmas.denotation_quorum] at h ⊢
    convert h using 2; ext q; simp [denotation]
    exact (inf_sup_right (α := 𝟯) _ _ _).symm
  have s4 : ⊨[μ] ⟐ₑ ([input, 𝟢]ₑ ∧ₑ (TF[echo₁]ₑ ∧ₑ TF[input]ₑ)) ∨ₑ ⟐ₑ ([input, 𝟣]ₑ ∧ₑ (TF[echo₁]ₑ ∧ₑ TF[input]ₑ)) := by
    intro p; have h := s3 default
    simp only [valid_pred, Lemmas.denotation_quorum, Lemmas.denotation_or,
        Lemmas.denotation_contraquorum] at h ⊢
    exact Corollary_2_4_6.t2 h
  have s5 : ⊨[μ] Tₑ (⟐ₑ ([input, 𝟢]ₑ ∧ₑ TF[echo₁]ₑ)) ∨ₑ Tₑ (⟐ₑ ([input, 𝟣]ₑ ∧ₑ TF[echo₁]ₑ)) := by
    intro p; have h3 := s4 default
    simp only [valid_pred, Lemmas.denotation_or] at h3
    simp only [valid_pred, Lemmas.denotation_T, Lemmas.denotation_or]
    simp [denotation, Lemmas.le_or] at h3 ⊢
    cases h3
    · next h =>
      left; intro y1 y2; specialize h y1 y2
      obtain ⟨h1, h2, h3⟩ := h; simp [Lemmas.le_and] at h3
      obtain ⟨h31, h32⟩ := h3; simp [Lemmas.or_le] at h32; obtain ⟨h32, h33⟩ := h32
      refine ⟨h1, h2, ?_⟩; simp only [Lemmas.and_true]; constructor
      · apply Lemmas.valid_and_TF h31 (h33 𝟢)
      · simp; intro v; rw [← Lemmas.valid_TF_iff_TF_true]; exact h32 v
    · next h =>
      right; intro y1 y2; specialize h y1 y2
      obtain ⟨h1, h2, h3⟩ := h; simp [Lemmas.le_and] at h3
      obtain ⟨h31, h32⟩ := h3; simp [Lemmas.or_le] at h32; obtain ⟨h32, h33⟩ := h32
      refine ⟨h1, h2, ?_⟩; simp only [Lemmas.and_true]; constructor
      · apply Lemmas.valid_and_TF h31 (h33 𝟣)
      · simp; intro v; rw [← Lemmas.valid_TF_iff_TF_true]; exact h32 v
  exact s5

theorem t2 : ⊨[μ] Tₑ (⟐ₑ [echo₁, 𝟢]ₑ) ∨ₑ Tₑ (⟐ₑ [echo₁, 𝟣]ₑ) := by
  intro p
  have s1 := t1 (μ := μ) default
  simp only [Lemmas.valid_or]
  cases Lemmas.valid_or.mp s1
  · next h =>
      left; clear s1; simp [denotation] at h ⊢
      intro y1 y2; specialize h y1 y2; obtain ⟨h1, h2, h3⟩ := h; simp [Lemmas.and_true] at h3
      have b := ca.CaEcho1! h1; simp only [Lemmas.valid_forall, substSimp, Lemmas.valid_impl] at b
      have b' := b 𝟢 ?_; simp [denotation] at b'; obtain ⟨h3, h4⟩ := h3
      refine ⟨_, h2, Lemmas.valid_and_TF b' (Lemmas.valid_TF_iff_TF_true.mpr (h4 𝟢))⟩
      · simp only [Lemmas.denotation_or, Lemmas.or_true]; simp [denotation]
        left; exact h3.1
  · next h =>
      right; clear s1; simp [denotation] at h ⊢
      intro y1 y2; specialize h y1 y2; obtain ⟨h1, h2, h3⟩ := h; simp [Lemmas.and_true] at h3
      have b := ca.CaEcho1! h1; simp only [Lemmas.valid_forall, substSimp, Lemmas.valid_impl] at b
      have b' := b 𝟣 ?_; simp [denotation] at b'; obtain ⟨h3, h4⟩ := h3
      exact ⟨_, h2, Lemmas.valid_and_TF b' (Lemmas.valid_TF_iff_TF_true.mpr (h4 𝟣))⟩
      · simp only [Lemmas.denotation_or, Lemmas.or_true]; simp [denotation]
        left; exact h3.1

theorem t3 : ⊨[μ] Tₑ (⊡ₑ [echo₁, 𝟢]ₑ) ∨ₑ Tₑ (⊡ₑ [echo₁, 𝟣]ₑ) := by
  have c := t2 (μ := μ) default; simp only [Lemmas.valid_or] at c
  have b := Lemma_5_3_8.t (μ := μ) (v := 𝟣); intro _
  simp only [Lemmas.valid_or]
  cases c
  · next h =>
      left; have h' : ⊨[μ] Tₑ (⟐ₑ [echo₁, 𝟢]ₑ) :=
        contraquorum_commut_T.mpr (contraquorum_global'.mp (contraquorum_commut_T' (p' := default) h))
      exact Lemma_5_3_8.t3 (Lemma_5_3_8.t2 h') _
  · next h =>
      right; have h' : ⊨[μ] Tₑ (⟐ₑ [echo₁, 𝟣]ₑ) :=
        contraquorum_commut_T.mpr (contraquorum_global'.mp (contraquorum_commut_T' (p' := default) h))
      exact Lemma_5_3_8.t3 (Lemma_5_3_8.t2 h') _

theorem t4 : ⊨[μ] □ₑ ([echo₂, 𝟢]ₑ ∨ₑ [echo₂, 𝟣]ₑ) := by
  have c := t3 (μ := μ) default; simp only [Lemmas.valid_or] at c
  cases c
  · next h1 =>
    intro _; simp [denotation] at h1 ⊢; intro p
    have b := ca.CaEcho2!_simp (v := 𝟢) (by simpa) p
    obtain ⟨b1, b2⟩ := b; simp [Lemmas.le_or]
    cases b1
    case v0 => grind
    case v1 => grind
    case vhalf =>
      cases Lemmas.byzantine_le_cases.mp b2
      · next h => grind [ca.CaCorrect'_byzantine (v' := 𝟢) h]
      · next h => have q := Lemma_5_3_5.t5 (μ := μ) (p := p)
                  simp [denotation] at q; rw [h] at q; contradiction
  · next h1 =>
    intro _; simp [denotation] at h1 ⊢; intro p
    have b := ca.CaEcho2!_simp (v := 𝟣) (by simpa) p
    obtain ⟨b1, b2⟩ := b; simp [Lemmas.le_or]
    cases b1
    case v0 => grind
    case v1 => grind
    case vhalf =>
      cases Lemmas.byzantine_le_cases.mp b2
      · next h => grind [ca.CaCorrect'_byzantine (v' := 𝟢) h]
      · next h => have q := Lemma_5_3_5.t5 (μ := μ) (p := p)
                  simp [denotation] at q; rw [h] at q; contradiction

theorem t5 : ⊨[μ] Tₑ (⊡ₑ ([echo₂, 𝟢]ₑ ∨ₑ [echo₂, 𝟣]ₑ)) := by
  intro _
  have t := t4 (μ := μ) default
  have b := ca.CaCorrect1 echo₂ default
  simp [denotation] at t b ⊢
  obtain ⟨b1, b2, b3⟩ := b; refine ⟨_, b2, ?_⟩
  intro x1 x2; simp [Lemmas.or_true]; specialize t x1; simp [Lemmas.le_or] at t
  cases t
  · next h => left; exact Lemmas.valid_and_TF h (by grind)
  · next h => right; exact Lemmas.valid_and_TF h (by grind)

end Corollary_5_3_10

namespace Proposition_5_3_11

variable
  {μ : Model Sig P Val}
  [ca : Thy μ]
  [twined : Twined3 μ.S]
  {v : Val}

theorem t : ⊨[μ] □ₑ (∃⁎ₑ [output]ₑ) := by
  have s1 := Corollary_5_3_10.t5 (μ := μ) default
  simp only [valid_pred, Lemmas.denotation_T, Lemmas.denotation_quorum, Lemmas.denotation_or, Lemmas.byzantine_le_T] at s1; simp [denotation] at s1
  obtain ⟨o1, o2, o3⟩ := s1
  have aff := ca.CaEcho2Affine
  have case1 : ∀ v, (∀ x ∈ o1, μ.ς echo₂ x v = 𝐭) →
      ⊨[μ] □ₑ (∃⁎ₑ [output]ₑ) := by
    intro v hv p; rw [← valid_iff_everywhere]; intro p'
    rw [Lemmas.valid_exist]; exists v; simp only [substSimp]
    have b := Lemmas.valid_forall.mp (ca.CaOutput! p') v
    simp only [substSimp] at b
    apply Lemmas.valid_impl.mp b
    simp [denotation]; exact ⟨o1, o2, hv⟩
  have case2 : (∃ x ∈ o1, μ.ς echo₂ x 𝟢 = 𝐭) →
      (∃ y ∈ o1, μ.ς echo₂ y 𝟣 = 𝐭) →
      ⊨[μ] □ₑ (∃⁎ₑ [output]ₑ) := by
    intro ⟨x, _, hx⟩ ⟨y, _, hy⟩
    have q0 := ca.CaEcho2?_simp hx
    have q1 := ca.CaEcho2?_simp hy
    intro p; rw [← valid_iff_everywhere]; intro p'
    rw [Lemmas.valid_exist]; exists ½; simp only [substSimp]
    have b := ca.CaOutput'! p'
    apply Lemmas.valid_impl.mp b
    have q0' : ⊨ (⊡(μ.S) (fun p => μ.ς echo₁ p 𝟢)) := by simpa [denotation] using Lemmas.valid_quorum.mp (q0 p')
    have q1' : ⊨ (⊡(μ.S) (fun p => μ.ς echo₁ p 𝟣)) := by simpa [denotation] using Lemmas.valid_quorum.mp (q1 p')
    have h0 := Remark_2_4_7.valid_quorum_implies_true (ca.CaCorrect_simp (v := 𝟢) echo₁) q0'
    have h1 := Remark_2_4_7.valid_quorum_implies_true (ca.CaCorrect_simp (v := 𝟣) echo₁) q1'
    simp [denotation, h0, h1]
  by_cases h : ∀ x ∈ o1, μ.ς echo₂ x 𝟢 = 𝐭
  · exact case1 𝟢 h
  · push_neg at h; obtain ⟨x, xm, hx⟩ := h
    have hx1 : μ.ς echo₂ x 𝟣 = 𝐭 := by
      have := Lemmas.or_true.mp (o3 x xm); tauto
    by_cases h' : ∀ y ∈ o1, μ.ς echo₂ y 𝟣 = 𝐭
    · exact case1 𝟣 h'
    · push_neg at h'; obtain ⟨y, ym, hy⟩ := h'
      have hy0 : μ.ς echo₂ y 𝟢 = 𝐭 := by
        have := Lemmas.or_true.mp (o3 y ym); tauto
      exact case2 ⟨y, ym, hy0⟩ ⟨x, xm, hx1⟩

end Proposition_5_3_11

namespace Lemma_5_4_2

variable
  {μ : Model Sig P Val}
  [ca : Thy μ]
  [twined : Twined3 μ.S]
  {v : Val}

omit twined in
theorem t1 : ⊨[μ] [input, v]ₑ ⇀ₑ (.val v =ₑ .val 𝟢) ∨ₑ (.val v =ₑ .val 𝟣) := by
  intro p; simp only [Lemmas.valid_impl]; intro h
  simp [denotation] at h ⊢
  cases v
  · simp
  · exfalso; have := ca.CaInput_half (p := p); rw [h] at this; contradiction
  · simp

omit twined in
theorem t2 : ⊨[μ] [echo₁, v]ₑ ⇀ₑ (.val v =ₑ .val 𝟢) ∨ₑ (.val v =ₑ .val 𝟣) := by
  intro p; simp only [Lemmas.valid_impl]; intro h
  simp [denotation] at h
  have ⟨p', hp'⟩ := ca.CaEcho1?_simp h
  have b := t1 (μ := μ) (v := v) p'; simp only [Lemmas.valid_impl] at b
  specialize b (by simpa [denotation] using hp')
  simp [valid_pred, denotation] at b ⊢; exact b

theorem t3 : ⊨[μ] [echo₂, v]ₑ ⇀ₑ (.val v =ₑ .val 𝟢) ∨ₑ (.val v =ₑ .val 𝟣) := by
  intro p; simp only [Lemmas.valid_impl]; intro h
  simp [denotation] at h
  have q1 := ca.CaEcho2?_simp h default
  simp only [Lemmas.valid_quorum] at q1
  have q2 := ca.CaCorrect_simp (v := v) echo₁
  have q1' := Theorem_2_4_5.t'' q1
  have t := Lemma_2_3_7.c3 q2 (by simpa [denotation] using q1')
  simp at t; obtain ⟨x1, x2⟩ := t
  have p2 := Lemmas.valid_impl.mp (t2 (μ := μ) (v := v) x1)
  simp [denotation] at p2 ⊢
  apply p2 x2

end Lemma_5_4_2

end CA
