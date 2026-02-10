-- NOTE the name of this file is temporary. Eventually code in this file will be reorganized

import mlda.Base
import mlda.Three
import mlda.FinSemitopology

open Three
open scoped Three.Atom

variable
  {Value : Type}
  [Fintype Value]
  -- [Nonempty Value] -- TODO is this needed?
  [DecidableEq Value]

namespace Definitions

variable
  (f : Value → 𝟯)
  (v v' : Value)

def allValues : Finset Value := Finset.univ

omit [DecidableEq Value] in
@[simp] theorem in_allValues : v ∈ allValues := Finset.mem_univ v

abbrev veq : 𝟯 := if v = v' then true else false
scoped infix:4 " ≡ " => veq

@[simp] def and_implies_eq : 𝟯 := (f v ∧ f v') → (v ≡ v')

@[simp] def and_implies_eq_all : 𝟯 :=
  allValues |>.fold min true fun v' => and_implies_eq f v v'

abbrev existence : 𝟯 := allValues |>.fold max false f
scoped notation " ∃⁎ " => existence

abbrev existence_affine : 𝟯 := allValues |>.fold min true (and_implies_eq_all f)
scoped notation " ∃₀₁ " => existence_affine

abbrev existence_unique : 𝟯 := existence f ∧ existence_affine f
scoped notation " ∃₁ " => existence_unique

end Definitions

open Definitions

namespace Lemmas

variable
  {f : Value → 𝟯}
  {v v' : Value}
  {a : 𝟯}

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

theorem byzantine_le_affine_implies_eq : .byzantine ≤ ∃₀₁ f → f v = .true → f v' = .true → v = v' := by
   intro h vt vt'; simp [existence_affine] at h
   have p := h v v'; simpa [vt, vt'] using p

theorem affine_implies_eq : ∃₀₁ f = .true → .byzantine ≤ f v → .byzantine ≤ f v' → v = v' := by
   intro h vt vt'; simp [existence_affine] at h
   simpa using Lemmas.mp_weak (h v v') (Lemmas.le_and.mpr ⟨vt, vt'⟩)

theorem unique_implies_existence_affine : a ≤ ∃₁ f → (a ≤ ∃⁎ f) ∧ (a ≤ ∃₀₁ f) := by
  intro h; simp [existence_unique] at h
  exact Lemmas.le_and.mp h

theorem unique_implies_affine : a ≤ ∃₁ f → a ≤ ∃₀₁ f := by
  intro h; exact unique_implies_existence_affine h |>.2

theorem unique_implies_existence : a ≤ ∃₁ f → a ≤ ∃⁎ f := by
  intro h; exact unique_implies_existence_affine h |>.1

end Lemmas

namespace Remark_3_1_2

open Lemmas

variable
  {f : Value → 𝟯}
  {v v' : Value}

theorem t1 : f v = .true → f v' = .true → v ≠ v'
  → ∃₀₁ f = .false := by
  intro v1 v2 n
  simp [existence_affine]
  exists v;
  exists v'; simpa [v1, v2]

theorem t2 : (∃! v, f v = .true) → (∀ v', f v' ≠ .byzantine) → ∃₁ f = .true := by
  rintro ⟨t, ft, h1⟩ h2
  simp [existence_unique, Lemmas.and_true]; constructor
  exists t; intro x y
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
    cases fx : f x <;> cases fy : f y <;> first | contradiction | simp <;> try exact ne_or_eq x y
    simp [hv x fx, hv y fy]
    exists v'; constructor; intro y
    cases fy : f y <;> first | contradiction | simp [h2]
    exists v; simp [h2, vt]; intro e; rw [e, vt] at h2; contradiction
  constructor; simp [existence_unique, affine, existence, Lemmas.le_join]
  exists v'; simp [h2]; exact affine

-- NOTE I think this theorem is not entirely true and not needed (see pdf). I think it should be removed. It is superseded by t5
-- theorem t4 : (∀ v, f v ≤ .byzantine) → (∃! v', f v' = .byzantine) → ∃₁ f = .byzantine ∧ ∃₀₁ f = .byzantine := by

theorem t5 : (∀ v, f v ≤ .byzantine) → v ≠ v' → f v = .byzantine → f v' = .byzantine → ∃₁ f = .byzantine := by
  rintro p ne fv fv'
  have affine : ∃₀₁ f = .byzantine := by
    simp [existence_affine]
    constructor
    · intro x y
      cases fx : f x <;> cases fy : f y <;> first | contradiction | simp <;> try exact ne_or_eq x y
      have := p x; rw [fx] at this; contradiction
    · exists v; simp [fv]; constructor; intro u; simp [Lemmas.le_or_implies]
      exists v'; simp [veq_false.mpr ne, fv']
  simp [existence_unique, affine, existence, Lemmas.le_join]
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
    simp [existence_unique, existence, existence_affine, Lemmas.le_and] at h
    obtain ⟨h1, h2⟩ := h
    constructor <;> assumption
  · intro ⟨h1, h2⟩
    rw [existence_unique]
    apply Lemmas.le_and.mpr
    constructor
    · simpa [existence]
    · simpa

end Part_2

namespace Part_3

abbrev P_A := ⊨ (T (∃₀₁ f))
abbrev P_B := (∃? v, .byzantine ≤ f v)

theorem A_B : P_A f ↔ P_B f := by
  simp [P_B]; constructor
  · intro h x y px py
    apply Lemmas.affine_implies_eq (by simp; exact h) px py
  · intro h
    simp [Lemmas.impl_true]; intro x y p
    obtain ⟨h1, h2⟩ := Lemmas.le_and.mp p
    apply_rules [p]

end Part_3

namespace Part_4

abbrev P_A := ⊨ (T (∃₁ f))
abbrev P_B := (∃! v, f v = .true) ∧ (∀ v, f v ≠ .byzantine)

theorem A_B : P_A f ↔ P_B f := by
  simp [P_B]; constructor
  · intro h; simp [existence_unique, Lemmas.and_true, existence, existence_affine] at h
    obtain ⟨⟨u, ut⟩, h2⟩ := h; constructor
    · exists u; constructor; assumption
      intro v vt
      simpa [Lemmas.and_true, ut, vt] using Lemmas.mp_weak (h2 v u)
    · intro v vb
      have e := by simpa [ut, vb] using h2 u v
      rw [e] at ut; rw [ut] at vb; contradiction
  rintro ⟨⟨u, ut, uu⟩, h2⟩
  simp [existence_unique, Lemmas.and_true, existence, existence_affine]; constructor
  · exists u
  · intro x y; simp [Lemmas.or_true]
    if xy : x = y then right; assumption
    else left; simp [Lemmas.and_false]
         cases fx : f x <;> cases fy : f y <;> first | contradiction | simp
         exact h2 x fx; exact h2 x fx; exact h2 y fy
         have xt := uu _ fx
         have yt := uu _ fy
         rw [← yt] at xt; contradiction

end Part_4

namespace Part_5

theorem t (h1 : (⊨ (∃₀₁ f) ∨ ⊨ (∃₁ f))) (h2 : ⊨ (T (f v ∧ f v'))) : v = v' := by
  simp at h1 h2
  obtain ⟨fv, fv'⟩ := Lemmas.and_true.mp h2
  cases h1
  next h => exact Lemmas.byzantine_le_affine_implies_eq (by simp; exact h) fv fv'
  next h => exact Lemmas.byzantine_le_affine_implies_eq (Lemmas.unique_implies_affine h) fv fv'

end Part_5

end Proposition_3_1_3

section Modal_Logic

section Types

inductive Term (V : Type) (scope : Nat) where
  | bound : Fin scope → Term V scope
  | val : V → Term V scope

inductive Expr (V P : Type) : Nat → Type where
  | term {n} : Term V n → Expr V P n
  | bot {n} : Expr V P n
  | neg {n} : Expr V P n → Expr V P n
  | and {n} : Expr V P n → Expr V P n → Expr V P n
  | quorum {n} : Expr V P n → Expr V P n
  | everywhere {n} : Expr V P n → Expr V P n
  | tf {n} : Expr V P n → Expr V P n
  | t {n} : Expr V P n → Expr V P n
  | predicate {n} : P → Term V n → Expr V P n
  | exist {n} : Expr V P (n +1) → Expr V P n
  | exist_affine {n} : Expr V P (n +1) → Expr V P n

def Interpretation (V P : Type) := P → V → 𝟯

structure Model (V : Type) [VFin : Fintype V] [ValuDec : DecidableEq V]
  (P : Type) [PFin : Fintype P] [PDef : DecidableEq P] [PNonempty : Nonempty P] where
  S : FinSemitopology P
  ς : Interpretation V P

end Types

namespace Notation

variable
  {V P : Type}
  [Fintype V]
  [DecidableEq V]
  [Fintype P]
  [DecidableEq P]
  [Nonempty P]
  {n : Nat}

scoped notation "¬ₑ " => Expr.neg
scoped notation "⊥ₑ" => Expr.bot
scoped infixl:35 " ∧ₑ " => Expr.and
scoped notation "⊡ₑ " => Expr.quorum
scoped notation "□ₑ " => Expr.everywhere
scoped notation "TFₑ " => Expr.tf
scoped notation "Tₑ " => Expr.t
scoped notation "∃⁎ₑ " => Expr.exist
scoped notation "∃₀₁ₑ " => Expr.exist_affine

abbrev somewhere (φ : Expr V P n) : Expr V P n := ¬ₑ (□ₑ (¬ₑ φ))
scoped notation "◇ₑ " => somewhere

abbrev contraquorum (φ : Expr V P n) : Expr V P n := ¬ₑ (⊡ₑ (¬ₑ φ))
scoped notation "⟐ₑ " => contraquorum

abbrev or {n : Nat} (φ ψ : Expr V P n) : Expr V P n := ¬ₑ (¬ₑ φ ∧ₑ ¬ₑ ψ)
scoped infixl:30 " ∨ₑ " => or

abbrev impl {n : Nat} (φ ψ : Expr V P n) : Expr V P n := ¬ₑ φ ∨ₑ ψ
scoped infixl:25 " →ₑ " => impl

abbrev for_all {n : Nat} (φ : Expr V P (n +1)) : Expr V P n := ¬ₑ (∃⁎ₑ (¬ₑ φ))
scoped notation "∀ₑ " => for_all

abbrev existence_unique {n : Nat} (φ : Expr V P (n +1)) : Expr V P n := ∃⁎ₑ φ ∧ₑ ∃₀₁ₑ φ
scoped notation "∃₁ₑ " => existence_unique

abbrev is_byzantine {n : Nat} (φ : Expr V P n) : Expr V P n := ¬ₑ (TFₑ φ)
scoped notation "Bₑ " => is_byzantine

scoped notation "[" p ", " t "]ₑ" => Expr.predicate p t
scoped notation "[" p "]ₑ" => Expr.predicate p (Term.bound 0)

-- abbrev T_all {n : Nat} (p : P) : Expr V P n := ∀ₑ (Tₑ [p]ₑ)
-- scoped notation "T[" p "]ₑ" => T_all p

abbrev TF_all {n : Nat} (p : P) : Expr V P n := ∀ₑ (TFₑ [p]ₑ)
scoped notation "TF[" p "]ₑ" => TF_all p

abbrev B_all {n : Nat} (p : P) : Expr V P n := ∀ₑ (Bₑ [p]ₑ)
scoped notation "B[" p "]ₑ" => B_all p

end Notation

open Notation

namespace Denotation

open scoped FinSemitopology

variable
  {V P : Type}
  [Fintype V]
  [DecidableEq V]
  [Fintype P]
  [DecidableEq P]
  [Nonempty P]
  (μ : Model V P)

@[simp] abbrev Term.substAt {n : Nat} (k : Fin (n + 1)) (v : V) (t : Term V (n + 1)) : Term V n :=
  match t with
  | .val w => .val w
  | .bound i =>
    if h : i = k then .val v
    else if h : i < k then .bound ⟨i, by omega⟩
    else .bound ⟨i - 1, by omega⟩

@[simp] def Expr.substAt {n : Nat} (k : Fin (n + 1)) (v : V) : Expr V P (n + 1) → Expr V P n
  | .term t        => .term (Term.substAt k v t)
  | .bot           => .bot
  | .neg e         => .neg (substAt k v e)
  | .and l r       => .and (substAt k v l) (substAt k v r)
  | .quorum e      => .quorum (substAt k v e)
  | .everywhere e  => .everywhere (substAt k v e)
  | .tf e          => .tf (substAt k v e)
  | .t e           => .t (substAt k v e)
  | .predicate p t => .predicate p (Term.substAt k v t)
  | .exist e       => .exist (substAt k.succ v e)
  | .exist_affine e => .exist_affine (substAt k.succ v e)

def Expr.size {n : Nat} : Expr V P n → Nat
  | .term _ | .bot | .predicate _ _ => 0
  | .and l r => Expr.size l + Expr.size r +1
  | .neg e | .quorum e | .everywhere e | .tf e | .t e | .exist e | .exist_affine e => Expr.size e +1

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Nonempty P] in
theorem Expr.substAt_size {n : Nat} (k : Fin (n + 1)) (v : V) (φ : Expr V P (n + 1)) :
  Expr.size (Expr.substAt k v φ) = Expr.size φ :=
  match φ with
  | .bot => by simp [Expr.size, Expr.substAt]
  | .neg e => by simp [Expr.size, Expr.substAt, Expr.substAt_size k v e]
  | .tf e => by simp [Expr.size, Expr.substAt, Expr.substAt_size k v e]
  | .quorum e => by simp [Expr.size, Expr.substAt, Expr.substAt_size k v e]
  | .predicate p t => by simp [Expr.size, Expr.substAt]
  | .t e => by simp [Expr.size, Expr.substAt, Expr.substAt_size k v e]
  | .everywhere e => by simp [Expr.size, Expr.substAt, Expr.substAt_size k v e]
  | .and l r => by simp [Expr.size, Expr.substAt, Expr.substAt_size k v l, Expr.substAt_size k v r]
  | .term t => by simp [Expr.size, Expr.substAt]
  | .exist e => by simp [Expr.size, Expr.substAt, Expr.substAt_size (n := n + 1) k.succ v e]
  | .exist_affine e => by simp [Expr.size, Expr.substAt, Expr.substAt_size (n := n + 1) k.succ v e]
                    
def denotation (φ : Expr V P 0) (p : P) : 𝟯 :=
  let denTerm (p' : P) (t : Term V 0) : 𝟯 := match t with
    | .val v => μ.ς p' v
  match φ, h : Expr.size φ with
  | .bot, _ => .false
  | .and l r, _ => denotation l p ∧ denotation r p
  | .tf e, _ => TF (denotation e p)
  | .t e, _ => T (denotation e p)
  | .neg e, _ => ¬ (denotation e p)
  | .quorum e, _ => ⊡(μ.S) (fun p => denotation e p)
  | .everywhere e, _ => □ (fun p => denotation e p)
  | .predicate p t, _ => denTerm p t
  | .term t, _ => denTerm p t
  | .exist e, _ => ∃⁎ (fun v => denotation (Expr.substAt 0 v e) p)
  | .exist_affine e, _ => ∃₀₁ (fun v => denotation (Expr.substAt 0 v e) p)
  termination_by Expr.size φ
  decreasing_by all_goals try simp [Expr.size, Expr.substAt_size] <;> omega

scoped notation  "ₛ[" φ ", " ix "↦" v "]" => Expr.substAt ix v φ
scoped notation "⟦" φ' "⟧ᵈ" => denotation (φ := φ')

abbrev valid_pred (p : P) (φ : Expr V P 0) : Prop := .byzantine ≤ ⟦ φ ⟧ᵈ μ p
abbrev valid (φ : Expr V P 0) := ∀ p, valid_pred μ p φ
abbrev model (Φ : Finset (Expr V P 0)) := ∀ φ ∈ Φ, valid μ φ
abbrev entails (Τ Φ : Finset (Expr V P 0)) := model μ Τ → model μ Φ

scoped notation p " ⊨[" μ "] " φ => valid_pred μ p φ
scoped notation "⊨[ " μ " ] " φ => valid μ φ
scoped notation "⊨*[ " μ " ] " Φ => model μ Φ
scoped notation Τ " ⊨*[" μ "] " Φ => entails μ Τ Φ

end Denotation

open Denotation

section Notation_3_2_4

variable
  {V P : Type}
  [Fintype V]
  [DecidableEq V]
  [Fintype P]
  [DecidableEq P]
  [Nonempty P]
  {μ : Model V P}
  {p : P}
  {φ : Expr V P 0}

theorem somewhere_global : (p ⊨[μ] (◇ₑ φ)) ↔ ⊨[μ] (◇ₑ φ) := by
  constructor
  · intro h p'; simp [denotation] at h ⊢; assumption
  · intro h; apply_rules

theorem everywhere_global : (p ⊨[μ] (□ₑ φ)) ↔ ⊨[μ] (□ₑ φ) := by
  constructor
  · intro h p'; simp [denotation] at h ⊢; assumption
  · intro h; apply_rules

theorem valid_iff_everywhere : (⊨[μ] φ) ↔ p ⊨[μ] (□ₑ φ) := by
  simp [valid, denotation]

theorem quorum_global : (p ⊨[μ] (⊡ₑ φ)) ↔ ⊨[μ] (⊡ₑ φ) := by
  constructor
  · intro h p'; simp [denotation] at h ⊢; assumption
  · intro h; apply_rules

theorem contraquorum_global : (p ⊨[μ] (⟐ₑ φ)) ↔ ⊨[μ] (⟐ₑ φ) := by
  constructor
  · intro h p'; simp [denotation] at h ⊢; assumption
  · intro h; apply_rules

end Notation_3_2_4

namespace Lemmas

open scoped FinSemitopology
open scoped Three.Function

variable
  {V P : Type}
  [Fintype V]
  [DecidableEq V]
  [Fintype P]
  [DecidableEq P]
  [Nonempty P]
  {μ : Model V P}
  {p : P}
  {n : Nat}
  {v : V}
  {φ ψ : Expr V P 0}
  {φ₁ : Expr V P 1}
  {Γ : List.Vector V n}

@[simp] theorem denotation_neg : ⟦¬ₑ φ⟧ᵈ μ p = (¬ ⟦φ⟧ᵈ μ p) := by
  simp [denotation]

@[simp] theorem denotation_or : ⟦φ ∨ₑ ψ⟧ᵈ μ p = (⟦φ⟧ᵈ μ p ∨ ⟦ψ⟧ᵈ μ p) := by
  simp [denotation]

theorem denotation_impl : ⟦φ →ₑ ψ⟧ᵈ μ p = (⟦φ⟧ᵈ μ p → ⟦ψ⟧ᵈ μ p) := by
  simp [denotation, Three.Atom.impl, Lemmas.neg_and]

theorem valid_or : (p ⊨[μ] φ ∨ₑ ψ) ↔ (p ⊨[μ] φ) ∨ p ⊨[μ] ψ := by
  simp [denotation, denotation, Lemmas.le_or]

theorem valid_impl : (p ⊨[μ] (φ →ₑ ψ)) ↔ ((⟦φ⟧ᵈ μ p = Three.true) → p ⊨[μ] ψ) := by
  simp [denotation, denotation, Lemmas.and_le]
  constructor
  · rintro (h | h)
    · intro h1; rw [h1] at h; contradiction
    · intro _; assumption
  · intro h; apply Decidable.or_iff_not_imp_left.mpr; simpa

axiom axiom_valid_exist : (p ⊨[μ] ∃⁎ₑ φ₁) ↔ (∃ v, p ⊨[μ] ₛ[φ₁, 0 ↦ v])

theorem axiom_valid_exist₁ : (p ⊨[μ] ∃⁎ₑ φ₁) ↔ (∃ v, p ⊨[μ] ₛ[φ₁, 0 ↦ v]) := by
  cases φ₁ <;> simp [denotation]

axiom axiom_valid_forall : (p ⊨[μ] ∀ₑ φ₁) ↔ (∀ v, p ⊨[μ] ₛ[φ₁, 0 ↦ v])

end Lemmas

section

variable
  {V : Type}
  [Fintype V]
  [Nonempty V]
  [DecidableEq V]

inductive Tag where
  | broadcast
  | echo
  | ready
  | deliver
  deriving DecidableEq, Nonempty, FinEnum

export Tag (broadcast echo ready deliver)

instance : Inhabited Tag := ⟨broadcast⟩

class ThyBB (μ : Model V Tag) where
  BrDeliver? : ⊨[μ] ∀ₑ ([deliver]ₑ →ₑ ⊡ₑ [ready]ₑ)
  BrReady? : ⊨[μ] ∀ₑ ([ready]ₑ →ₑ ⊡ₑ [echo]ₑ)
  BrEcho? : ⊨[μ] ∀ₑ ([echo]ₑ →ₑ ◇ₑ [broadcast]ₑ)
  BrDeliver! : ⊨[μ] ∀ₑ (⊡ₑ [ready]ₑ →ₑ [deliver]ₑ)
  BrReady! : ⊨[μ] ∀ₑ (⊡ₑ [echo]ₑ →ₑ [ready]ₑ)
  BrEcho! : ⊨[μ] ∀ₑ (◇ₑ [broadcast]ₑ →ₑ ∃⁎ₑ [echo]ₑ)
  BrReady!! : ⊨[μ] ∀ₑ (⟐ₑ [ready]ₑ →ₑ ∃⁎ₑ [ready]ₑ)
  BrEcho01 : ⊨[μ] ∃₀₁ₑ [echo]ₑ
  BrBroadast1 : ⊨[μ] ∃₁ₑ (◇ₑ [broadcast]ₑ)
  BrCorrect : ⊨[μ] ∀ₑ (⊡ₑ TF[ready]ₑ ∧ₑ ⊡ₑ TF[echo]ₑ)
  BrCorrectReady : ⊨[μ] ∀ₑ (TF[ready]ₑ ∨ₑ B[ready]ₑ) -- BrCorrect'
  BrCorrectEcho : ⊨[μ] ∀ₑ (TF[echo]ₑ ∨ₑ B[echo]ₑ) -- BrCorrect'
  BrCorrectBroadcast : ⊨[μ] (□ₑ TF[broadcast]ₑ ∨ₑ □ₑ B[broadcast]ₑ) -- BrCorrect''

end

namespace Lemma_4_2_4

variable
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  (μ : Model V Tag)
  [bb : ThyBB μ]
  {p : Tag}
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
                intro x; have k := Lemmas.byzantine_le_TF.mp (h v)
                contradiction
              · have b := bb.BrBroadast1 default
                simp [denotation, existence, Lemmas.le_and] at b
                have ⟨⟨v, b1⟩, b2⟩ := b; clear b
                exists v; simp [denotation] at h ⊢;
                have : Model.ς μ broadcast v = Three.true := by
                  specialize h v; simp [Lemmas.byzantine_le_TF] at h
                  cases Lemmas.byzantine_le.mp b1; contradiction; assumption
                constructor
                · assumption
                · intro u fx; specialize b2 u v;
                  simp [Lemmas.le_or_implies] at b2; apply_rules
  · next h => right; intro v p; simp [denotation];
              simp [denotation, FinSemitopology.everywhere, existence] at h
              exact h v

end Lemma_4_2_4

namespace Lemmas

variable
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {μ : Model V Tag}
  [bb : ThyBB μ]
  {p : Tag}
  {v : V}

theorem when_broadcast : (Model.ς μ broadcast v = .true) →
  Lemma_4_2_4.P1 μ ∧ (∀ v', byzantine ≤ Model.ς μ broadcast v' → v = v') := by
  intro h; cases Lemma_4_2_4.t μ
  next k => constructor
            · assumption
            · intro v' pv; obtain ⟨h1, ⟨w, p2, q1⟩⟩ := k
              specialize h1 default; simp [denotation] at h1
              have helper : ∀ {u}, byzantine ≤ Model.ς μ broadcast u → Model.ς μ broadcast u = Three.true := by
                intro u pu; cases Lemmas.byzantine_le.mp pu
                · next h => have x := h1 u; simp [Lemmas.byzantine_le_TF] at x; contradiction
                · next h => assumption
              have d1 := q1 v' (by intro p; simp [denotation]; exact helper pv)
              have d2 := q1 v (by intro p; simp [denotation]; assumption)
              subst_vars; rfl
  next k => simp [Lemma_4_2_4.P2, denotation] at k; specialize k v; rw [h] at k; contradiction

end Lemmas

namespace Lemma_4_2_6

variable
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {μ : Model V Tag}
  [bb : ThyBB μ]
  {v : V}

theorem t2 : ⊨[μ] (◇ₑ [broadcast, .val v]ₑ →ₑ □ₑ [echo, .val v]ₑ) := by
  intro p; rw [Lemmas.valid_impl]; simp [denotation]; intro h
  have i := bb.BrEcho! p; simp [denotation] at i; specialize i v
  simp [Lemmas.le_or] at i; apply Decidable.or_iff_not_imp_left.mp at i; simp at i; specialize i h
  obtain ⟨v', pv⟩ := i
  have j := bb.BrCorrectEcho p; simp [denotation] at j; specialize j v'; simp [Lemmas.and_le] at j
  cases j
  · next k => simp at k; specialize k v'
              have q := Three.Atom.Proposition_2_2_2.p8 (a := Model.ς μ echo v')
              simp at q; replace q := q.mp pv; simp [q] at k
              have brecho? := bb.BrEcho? p; simp [denotation] at brecho?; specialize brecho? v'
              simp [Lemmas.and_le] at brecho?; cases brecho?
              next u => rw [k] at u; contradiction
              next u => rwa [Lemmas.when_broadcast h |>.2 v' u]
  · next k => rw [k v]

theorem t1 : ⊨[μ] (◇ₑ [broadcast, .val v]ₑ →ₑ [echo, .val v]ₑ) := by
  intro p; rw [Lemmas.valid_impl]; intro h
  have h1 : p ⊨[μ] (◇ₑ [broadcast, .val v]ₑ →ₑ □ₑ [echo, .val v]ₑ) := t2 p
  rw [Lemmas.valid_impl] at h1;
  specialize h1 h; apply valid_iff_everywhere.mpr at h1; exact h1 p

-- theorem t3 : ⊨[μ] (⊡ₑ [echo, .val v]ₑ →ₑ □ₑ [ready, .val v]ₑ) := by
--   intro p; rw [Lemmas.valid_impl]; intro h; simp only at h
--   have b := bb.BrReady! p
--   simp [denotation, go] at b; specialize b v; simp [Lemmas.and_le] at b

end Lemma_4_2_6

end Modal_Logic
