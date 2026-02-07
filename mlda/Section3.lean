-- NOTE the name of this file is temporary. Eventually code in this file will be reorganized

import mlda.Base
import mlda.Three

variable
  {Value : Type}
  [Fintype Value]
  -- [Nonempty Value] -- TODO is this needed?
  [DecidableEq Value]

namespace Definitions

variable
  (f : Value → 𝟯)
  (v v' : Value)

open scoped Three.Atom
open Three

def allValues : Finset Value := Finset.univ

omit [DecidableEq Value] in
@[simp] theorem in_allValues : v ∈ allValues := Finset.mem_univ v

abbrev veq : 𝟯 := if v = v' then true else false
scoped infix:4 " ≡ " => veq

@[simp] def and_implies_eq : 𝟯 := (f v ∧ f v') → (v ≡ v')

@[simp] def and_implies_eq_all : 𝟯 :=
  allValues |>.fold min true fun v' => and_implies_eq f v v'

def existence : 𝟯 := allValues |>.fold max false f
scoped notation " ∃⁎ " => existence

def existence_affine : 𝟯 := allValues |>.fold min true (and_implies_eq_all f)
scoped notation " ∃₀₁ " => existence_affine

def existence_unique : 𝟯 := existence f ∧ existence_affine f
scoped notation " ∃₁ " => existence_unique

end Definitions

open Definitions

namespace Lemmas

variable
  {f : Value → 𝟯}
  {v v' : Value}

omit [Fintype Value] in
@[simp] theorem veq_true : (v ≡ v') = .true ↔ v = v' := by simp

omit [Fintype Value] in
@[simp] theorem veq_false : (v ≡ v') = .false ↔ v ≠ v' := by simp

omit [Fintype Value] in
@[simp] theorem veq_refl : (v ≡ v) = .true := by simp

omit [Fintype Value] in
@[simp] theorem veq_byzantine_le: .byzantine ≤ (v ≡ v') ↔ (v ≡ v') = .true := by
  if h : v = v'
  then simp [h]
  else simp [veq_false.mpr h]

omit [Fintype Value] in
@[simp] theorem veq_le_byzantine : (v ≡ v') ≤ .byzantine ↔ (v ≡ v') = .false := by
  if h : v = v'
  then simp [h]
  else simp [veq_false.mpr h]

omit [Fintype Value] in
@[simp] theorem veq_ne_byzantine : (v ≡ v') ≠ .byzantine := by
  if h : v = v'
  then simp [h]
  else simp [veq_false.mpr h]

end Lemmas

namespace Remark_3_1_2

open scoped Three.Atom
open Lemmas

variable
  {f : Value → 𝟯}
  {v v' : Value}

theorem t1 : f v = .true → f v' = .true → v ≠ v'
  → ∃₀₁ f = .false := by
  intro v1 v2 n
  simp [existence_affine]
  exists v;
  exists v'; simp [v1, v2, Lemmas.veq_false.mpr n]

theorem t2 : (∃! v, f v = .true) → (∀ v', f v' ≠ .byzantine) → ∃₁ f = .true := by
  rintro ⟨t, ft, h1⟩ h2
  simp [existence_unique, Three.Lemmas.and_true]; constructor
  simp [existence]
  exists t
  simp [existence_affine, and_implies_eq_all, and_implies_eq]; intro x y
  have hx := h2 x; have hy := h2 y
  cases fx : f x <;> first | contradiction | simp
  cases fy : f y <;> first | contradiction | simp
  simp [h1 x fx, h1 y fy]

theorem t3 : (∃! v, f v = .true) → f v' = .byzantine
  → ∃₁ f = .byzantine ∧ ∃₀₁ f = .byzantine := by
  rintro ⟨v, vt, hv⟩ h2
  have affine : ∃₀₁ f = .byzantine := by
    simp [existence_affine]
    constructor
    intro x; intro y
    rw [Three.Lemmas.byzantine_le]
    cases fx : f x <;> cases fy : f y <;> first | contradiction | simp <;> try exact ne_or_eq x y
    simp [hv x fx, hv y fy]
    exists v'; constructor; intro y
    cases fy : f y <;> first | contradiction | simp [h2]
    exists v; simp [h2, vt]; intro e; rw [e, vt] at h2; contradiction
  constructor; simp [existence_unique, affine, existence, Three.Lemmas.le_join]
  exists v'; simp [h2]; exact affine

-- NOTE I think this theorem is not entirely true and not needed (see pdf). I think it should be removed. It is superseded by t5
-- theorem t4 : (∀ v, f v ≤ .byzantine) → (∃! v', f v' = .byzantine) → ∃₁ f = .byzantine ∧ ∃₀₁ f = .byzantine := by

theorem t5 : (∀ v, f v ≤ .byzantine) → v ≠ v' → f v = .byzantine → f v' = .byzantine → ∃₁ f = .byzantine := by
  rintro p ne fv fv'
  have affine : ∃₀₁ f = .byzantine := by
    simp [existence_affine]
    constructor
    · intro x y
      rw [Three.Lemmas.byzantine_le]
      cases fx : f x <;> cases fy : f y <;> first | contradiction | simp <;> try exact ne_or_eq x y
      have := p x; rw [fx] at this; contradiction
    · exists v; simp [fv]; constructor
      intro y; simp [Three.Lemmas.byzantine_le_impl];
      exists v'; simp [veq_false.mpr ne, fv']
  simp [existence_unique, affine, existence, Three.Lemmas.le_join]
  exists v; simp [fv]

theorem t6 : (∀ v, f v = .false) → ∃₁ f = .false ∧ ∃₀₁ f = .true := by
  intro h
  have affine : ∃₀₁ f = .true := by simp [existence_affine]; intro x y; simp [h x, h y]
  have ex : ∃⁎ f = .false := by simpa [existence]
  have unique : ∃₁ f = .false := by simp [existence_unique, ex]
  exact ⟨unique, affine⟩

end Remark_3_1_2

namespace Proposition_3_1_3

open Three.Atom

variable
  (f : Value → 𝟯)
  {v v' : Value}

namespace Part_1

abbrev p_A := ⊨ (∃₀₁ f)
abbrev p_B := .byzantine ≤ ∃₀₁ f
abbrev p_C := ∃? v, ⊨ (T (f v))
abbrev p_D := ∃? v, f v = .true
abbrev p_E := ∀ v v', f v = .true → f v' = .true → v = v'

theorem A_B : p_A f → p_B f := by simp

theorem B_C : p_B f → p_C f := by
  simp [existence_affine]; intro h x y h2 h3
  simp at h2 h3; have hx := h x y; simpa [h2, h3] using hx

omit [Fintype Value] [DecidableEq Value] in
theorem C_D : p_C f → p_D f := by simp [p_C]

omit [Fintype Value] [DecidableEq Value] in
theorem D_E : p_D f → p_E f := by
  simp [p_D, p_E]; intro h x y fx fy
  exact h fx fy

theorem E_A : p_E f → p_A f := by
  simp [p_E, existence_affine]; intro h x y
  cases fx : f x <;> cases fy : f y <;> first | contradiction | simp
  simp [h x y fx fy]

end Part_1

namespace Part_2

abbrev P_A := ⊨ (∃₁ f)
abbrev P_B := (∃ v, ⊨ (f v)) ∧ ⊨ (∃₀₁ f)

theorem A_B : P_A f ↔ P_B f := by
  simp [P_B]; constructor
  · intro h
    simp [existence_unique, existence, existence_affine, Three.Lemmas.le_and] at h
    obtain ⟨h1, h2⟩ := h
    simp [existence_affine]
    constructor <;> assumption
  · intro ⟨h1, h2⟩
    rw [existence_unique]
    apply Three.Lemmas.le_and.mpr
    constructor
    · simpa [existence]
    · assumption

end Part_2

namespace Part_3

abbrev P_A := ⊨ (T (∃₀₁ f))
abbrev P_B := (∃? v, f v = .true) ∧ (∀ v, f v ≠ .byzantine)

-- theorem A_B : P_A f ↔ P_B f := by
--   simp [P_B]; constructor
--   · intro h
--     simp [existence_affine] at h
--     constructor
--     · intro a b ta tb;
--       simpa [ta, tb] using h a b
--     · intro v b
--       sorry
      
  --   obtain ⟨⟨u, fu⟩, h2⟩ := h
  --   constructor; 
  --   · intro a b ta tb
  --     simpa [ta, tb] using h2 a b
  --   · intro v e
  --     have p := h2 u v
  --     have uv : u ≠ v := sorry
  --     conv at p => left; right; rw [Lemmas.veq_false.mpr uv]
  --     simp [Three.Lemmas.and_false] at p; cases p
  --     next h => rw [fu] at h; contradiction
  --     next h => rw [e] at h; contradiction
  -- · rintro ⟨h1, h2⟩
  --   simp [existence_unique, Three.Lemmas.and_true, existence, existence_affine]; constructor
  --   · 
end Part_3

namespace Part_4

abbrev P_A := ⊨ (T (∃₁ f))
abbrev P_B := (∃! v, f v = .true) ∧ (∀ v, f v ≠ .byzantine)

theorem A_B : P_A f ↔ P_B f := by
  simp [P_B]; constructor
  · intro h; simp [existence_unique, Three.Lemmas.and_true, existence, existence_affine] at h
    obtain ⟨⟨u, ut⟩, h2⟩ := h; constructor
    · exists u; constructor; assumption
      intro v vt
      simpa [Three.Lemmas.and_true, ut, vt] using Three.Lemmas.mp_weak (h2 v u)
    · intro v vb
      have e := by simpa [ut, vb] using h2 u v
      rw [e] at ut; rw [ut] at vb; contradiction
  rintro ⟨⟨u, ut, uu⟩, h2⟩
  simp [existence_unique, Three.Lemmas.and_true, existence, existence_affine]; constructor
  · exists u
  · intro x y; simp [Three.Lemmas.or_true]
    if xy : x = y then right; assumption
    else left; simp [Three.Lemmas.and_false]
         cases fx : f x <;> cases fy : f y <;> first | contradiction | simp
         exact h2 x fx; exact h2 x fx; exact h2 y fy
         have xt := uu _ fx
         have yt := uu _ fy
         rw [← yt] at xt; contradiction

end Part_4

end Proposition_3_1_3
