-- NOTE the name of this file is temporary. Eventually code in this file will be reorganized

import mlda.Base
import mlda.Three

variable
  {Value : Type}
  [Fintype Value]
  [Nonempty Value]
  [DecidableEq Value]

namespace Definitions

variable 
  (f : Value → 𝟯)
  (v v' : Value)

open scoped Three.Atom
open Three

def allValues : Finset Value := Finset.univ

omit [Nonempty Value] [DecidableEq Value] in
@[simp] theorem in_allValues : v ∈ allValues := Finset.mem_univ v

abbrev veq : 𝟯 := if v = v' then true else false
scoped infix:4 " ≡ " => veq

def and_implies_eq : 𝟯 := (f v ∧ f v') → (v ≡ v')

def and_implies_eq_all : 𝟯 :=
  allValues |>.fold min true fun v' => and_implies_eq f v v'

def existence : 𝟯 := allValues |>.fold max false f
scoped notation " ∃ " => existence

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

omit [Fintype Value] [Nonempty Value] in 
@[simp] theorem veq_true : (v ≡ v') = .true ↔ v = v' := by simp 

omit [Fintype Value] [Nonempty Value] in 
@[simp] theorem veq_false : (v ≡ v') = .false ↔ v ≠ v' := by simp

omit [Fintype Value] [Nonempty Value] in 
@[simp] theorem veq_refl : (v ≡ v) = .true := by simp

omit [Fintype Value] [Nonempty Value] in 
@[simp] theorem veq_le_byzantine : (v ≡ v') ≤ .byzantine ↔ (v ≡ v') = .false := by 
  if h : v = v' 
  then simp [h]
  else simp [veq_false.mpr h]

omit [Fintype Value] [Nonempty Value] in 
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

omit [Nonempty Value] in 
theorem t1 : f v = .true → f v' = .true → v ≠ v' 
  → ∃₀₁ f = .false := by
  intro v1 v2 n
  simp [existence_affine]
  exists v; simp [and_implies_eq_all, and_implies_eq]
  exists v'; simp [v1, v2, Lemmas.veq_false.mpr n]

omit [Nonempty Value] in
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

omit [Nonempty Value] in
theorem t3 : (∃! v, f v = .true) → f v' = .byzantine 
  → ∃₁ f = .byzantine ∧ ∃₀₁ f = .byzantine := by
  rintro ⟨v, vt, hv⟩ h2
  have affine : ∃₀₁ f = .byzantine := by
    simp [existence_affine]
    constructor
    intro x; simp [and_implies_eq_all, and_implies_eq]; intro y
    rw [Three.Lemmas.byzantine_le]
    cases fx : f x <;> cases fy : f y <;> first | contradiction | simp <;> try exact ne_or_eq x y
    simp [hv x fx, hv y fy]
    exists v'; simp [and_implies_eq_all, and_implies_eq]; constructor; intro y
    cases fy : f y <;> first | contradiction | simp [h2]
    exists v; simp [h2, vt]; intro e; rw [e, vt] at h2; contradiction
  constructor; simp [existence_unique, affine, existence, Three.Lemmas.le_join]
  exists v'; simp [h2]; exact affine

-- NOTE I think this theorem is not entirely true and not needed (see pdf). I think it should be removed. It is superseded by t5
-- theorem t4 : (∀ v, f v ≤ .byzantine) → (∃! v', f v' = .byzantine) → ∃₁ f = .byzantine ∧ ∃₀₁ f = .byzantine := by

omit [Nonempty Value] in
theorem t5 : (∀ v, f v ≤ .byzantine) → v ≠ v' → f v = .byzantine → f v' = .byzantine → ∃₁ f = .byzantine := by 
  rintro p ne fv fv'
  have affine : ∃₀₁ f = .byzantine := by
    simp [existence_affine]
    constructor
    · intro x; simp [and_implies_eq_all, and_implies_eq]; intro y
      rw [Three.Lemmas.byzantine_le]
      cases fx : f x <;> cases fy : f y <;> first | contradiction | simp <;> try exact ne_or_eq x y
      have := p x; rw [fx] at this; contradiction
    · exists v
      simp [and_implies_eq_all, and_implies_eq, fv]
      constructor
      intro y; simp [Three.Lemmas.byzantine_le_impl]; 
      exists v'; simp [veq_false.mpr ne, fv']
  simp [existence_unique, affine, existence, Three.Lemmas.le_join]
  exists v; simp [fv]

     
end Remark_3_1_2
