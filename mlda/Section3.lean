-- NOTE the name of this file is temporary. Eventually code in this file will be reorganized

import mlda.Base
import mlda.Three
import mlda.FinSemitopology
import Mathlib.Tactic.Attr.Register

open Three
open scoped Three.Atom
open scoped Three.Function
open FinSemitopology

variable
  {Value : Type}
  [Fintype Value]
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

theorem byzantine_le_affine_implies_eq : .byzantine ≤ ∃₀₁ f ↔ (∀ {v} {v'}, f v = .true → f v' = .true → v = v') := by
  constructor; intro h v v' vt vt'; simp [existence_affine] at h;
  have p := h v v'; simpa [vt, vt'] using p
  intro h; simp; intro v v'; simp [Lemmas.le_or_implies, Lemmas.and_true]; apply h

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
  next h => exact Lemmas.byzantine_le_affine_implies_eq.mp (by simp; exact h) fv fv'
  next h => exact Lemmas.byzantine_le_affine_implies_eq.mp (Lemmas.unique_implies_affine h) fv fv'

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

@[simp] def impl {n : Nat} (φ ψ : Expr V P n) : Expr V P n := ¬ₑ φ ∨ₑ ψ
scoped infixl:25 " →ₑ " => impl

abbrev for_all {n : Nat} (φ : Expr V P (n +1)) : Expr V P n := ¬ₑ (∃⁎ₑ (¬ₑ φ))
scoped notation "∀ₑ " => for_all

abbrev existence_unique {n : Nat} (φ : Expr V P (n +1)) : Expr V P n := ∃⁎ₑ φ ∧ₑ ∃₀₁ₑ φ
scoped notation "∃₁ₑ " => existence_unique

abbrev is_byzantine {n : Nat} (φ : Expr V P n) : Expr V P n := ¬ₑ (TFₑ φ)
scoped notation "Bₑ " => is_byzantine

scoped notation "[" p ", " t "]ₑ" => Expr.predicate p t
scoped notation "[" p "]ₑ" => Expr.predicate p (Term.bound 0)

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

@[simp] def substAt {n : Nat} (k : Fin (n + 1)) (v : V) : Expr V P (n + 1) → Expr V P n
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
theorem substAt_size {n : Nat} (k : Fin (n + 1)) (v : V) (φ : Expr V P (n + 1)) :
  Expr.size (substAt k v φ) = Expr.size φ :=
  match φ with
  | .bot => by simp [Expr.size, substAt]
  | .neg e => by simp [Expr.size, substAt, substAt_size k v e]
  | .tf e => by simp [Expr.size, substAt, substAt_size k v e]
  | .quorum e => by simp [Expr.size, substAt, substAt_size k v e]
  | .predicate p t => by simp [Expr.size, substAt]
  | .t e => by simp [Expr.size, substAt, substAt_size k v e]
  | .everywhere e => by simp [Expr.size, substAt, substAt_size k v e]
  | .and l r => by simp [Expr.size, substAt, substAt_size k v l, substAt_size k v r]
  | .term t => by simp [Expr.size, substAt]
  | .exist e => by simp [Expr.size, substAt, substAt_size (n := n + 1) k.succ v e]
  | .exist_affine e => by simp [Expr.size, substAt, substAt_size (n := n + 1) k.succ v e]

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
  | .exist e, _ => ∃⁎ (fun v => denotation (substAt 0 v e) p)
  | .exist_affine e, _ => ∃₀₁ (fun v => denotation (substAt 0 v e) p)
  termination_by Expr.size φ
  decreasing_by all_goals try simp [Expr.size, substAt_size] <;> omega

scoped notation  "ₛ[" φ ", " ix "↦" v "]" => substAt ix v φ
scoped notation "⟦" φ' "⟧ᵈ" => denotation (φ := φ')

abbrev valid_pred (p : P) (φ : Expr V P 0) : Prop := .byzantine ≤ ⟦ φ ⟧ᵈ μ p
abbrev valid (φ : Expr V P 0) := ∀ p, valid_pred μ p φ

scoped notation p " ⊨[" μ "] " φ => valid_pred μ p φ
scoped notation "⊨[" μ "] " φ => valid μ φ

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
  {p p' : P}
  {φ : Expr V P 0}

theorem den_somewhere_global (p p' : P) : ⟦◇ₑ φ⟧ᵈ μ p = ⟦◇ₑ φ⟧ᵈ μ p' := by simp [denotation]
theorem somewhere_global : (p ⊨[μ] (◇ₑ φ)) → p' ⊨[μ] (◇ₑ φ) := by simp [den_somewhere_global p p']

theorem den_everywhere_global (p p' : P) : ⟦□ₑ φ⟧ᵈ μ p = ⟦□ₑ φ⟧ᵈ μ p' := by simp [denotation]
theorem everywhere_global : (p ⊨[μ] (□ₑ φ)) → p' ⊨[μ] (□ₑ φ) := by simp [den_everywhere_global p p']

theorem valid_iff_everywhere : (⊨[μ] φ) ↔ p ⊨[μ] (□ₑ φ) := by
  simp [valid, denotation]

theorem den_quorum_global (p p' : P) : ⟦⊡ₑ φ⟧ᵈ μ p = ⟦⊡ₑ φ⟧ᵈ μ p' := by simp [denotation]
theorem quorum_global : (p ⊨[μ] (⊡ₑ φ)) → p' ⊨[μ] (⊡ₑ φ) := by simp [den_quorum_global p p']
theorem quorum_global' : (p ⊨[μ] (⊡ₑ φ)) ↔ ⊨[μ] (⊡ₑ φ) := by
  constructor <;> intro h
  intro p'; apply quorum_global h
  exact h p

theorem den_contraquorum_global (p p' : P) : ⟦⟐ₑ φ⟧ᵈ μ p = ⟦⟐ₑ φ⟧ᵈ μ p' := by simp [denotation]
theorem contraquorum_global : (p ⊨[μ] (⟐ₑ φ)) → p' ⊨[μ] (⟐ₑ φ) := by simp [den_contraquorum_global p p']

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
  {p p' : P}
  {n : Nat}
  {k : Fin (n + 1)}
  {v : V}
  {φ ψ : Expr V P 0}
  {α β : Expr V P (n + 1)}
  {φ₁ : Expr V P 1}
  {Γ : List.Vector V n}

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Nonempty P] in
@[substSimp] theorem substAt_impl : ₛ[α →ₑ β, k ↦ v] = (ₛ[α, k ↦ v] →ₑ ₛ[β, k ↦ v]) := by simp

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Nonempty P] in
@[substSimp] theorem substAt_or : ₛ[α ∨ₑ β, k ↦ v] = (ₛ[α, k ↦ v] ∨ₑ ₛ[β, k ↦ v]) := by simp

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Nonempty P] in
@[substSimp] theorem substAt_and : ₛ[α ∧ₑ β, k ↦ v] = (ₛ[α, k ↦ v] ∧ₑ ₛ[β, k ↦ v]) := by simp

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Nonempty P] in
@[substSimp] theorem substAt_tf : ₛ[TFₑ α, k ↦ v] = TFₑ ₛ[α, k ↦ v] := by simp

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Nonempty P] in
@[substSimp] theorem substAt_tf_all : ₛ[TF[p]ₑ, k ↦ v] = TF[p]ₑ := by
  simp; intro q; exact absurd q (Fin.succ_ne_zero k).symm

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Nonempty P] in
@[substSimp] theorem substAt_somewhere : ₛ[◇ₑ α, k ↦ v] = (◇ₑ ₛ[α, k ↦ v]) := by simp

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Nonempty P] in
@[substSimp] theorem substAt_quorum : ₛ[⊡ₑ α, k ↦ v] = (⊡ₑ ₛ[α, k ↦ v]) := by simp

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Nonempty P] in
@[substSimp] theorem substAt_predicate {t : Term V (n +1)}
  : ₛ[[ p, t]ₑ, k ↦ v] = [p, Term.substAt k v t]ₑ := by simp [substAt]

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Nonempty P] in
@[substSimp] theorem substAt_bound {n : Nat} : Term.substAt (n := n) 0 v (.bound 0) = .val (scope := n) v := by simp

@[simp] theorem denotation_neg : ⟦¬ₑ φ⟧ᵈ μ p = (¬ ⟦φ⟧ᵈ μ p) := by
  simp [denotation]

@[simp] theorem denotation_or : ⟦φ ∨ₑ ψ⟧ᵈ μ p = (⟦φ⟧ᵈ μ p ∨ ⟦ψ⟧ᵈ μ p) := by
  simp [denotation]

theorem denotation_impl : ⟦φ →ₑ ψ⟧ᵈ μ p = (⟦φ⟧ᵈ μ p → ⟦ψ⟧ᵈ μ p) := by
  simp [denotation, Three.Atom.impl, Lemmas.neg_and]

theorem denotation_everywhere : ⟦□ₑ φ⟧ᵈ μ p = □ (fun p => ⟦φ⟧ᵈ μ p) := by
  simp [denotation]

theorem denotation_somewhere : ⟦◇ₑ φ⟧ᵈ μ p = ◇ (fun p => ⟦φ⟧ᵈ μ p) := by
  simp [denotation, ← Lemmas.join_neg]; congr; ext k; simp

theorem denotation_predicate : ⟦[p, .val v]ₑ⟧ᵈ μ p' = μ.ς p v  := by
  simp [denotation]

theorem denotation_exists_affine : ⟦∃₀₁ₑ φ₁⟧ᵈ μ p = ∃₀₁ (fun v => ⟦ₛ[φ₁, 0 ↦ v]⟧ᵈ μ p) := by
  simp [denotation]

@[simp] theorem valid_T : (p ⊨[μ] Tₑ φ) ↔ ⟦φ⟧ᵈ μ p = .true := by
  simp [denotation, denotation]

theorem valid_or : (p ⊨[μ] φ ∨ₑ ψ) ↔ (p ⊨[μ] φ) ∨ p ⊨[μ] ψ := by
  simp [denotation, denotation, Lemmas.le_or]

theorem valid_and : (p ⊨[μ] φ ∧ₑ ψ) ↔ (p ⊨[μ] φ) ∧ p ⊨[μ] ψ := by
  simp [denotation, denotation, Lemmas.le_and]

theorem valid_impl : (p ⊨[μ] (φ →ₑ ψ)) ↔ ((⟦φ⟧ᵈ μ p = Three.true) → p ⊨[μ] ψ) := by
  simp [denotation, denotation, Lemmas.and_le]
  constructor
  · rintro (h | h)
    · intro h1; rw [h1] at h; contradiction
    · intro _; assumption
  · intro h; apply Decidable.or_iff_not_imp_left.mpr; simpa

theorem valid_exist : (p ⊨[μ] ∃⁎ₑ φ₁) ↔ (∃ v, p ⊨[μ] ₛ[φ₁, 0 ↦ v]) := by
  cases φ₁ <;> simp [denotation]

theorem valid_forall : (p ⊨[μ] ∀ₑ φ₁) ↔ (∀ v, p ⊨[μ] ₛ[φ₁, 0 ↦ v]) := by
  cases φ₁ <;> simp [denotation]

end Lemmas

section

variable
  {V : Type}
  [Fintype V]
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

theorem BrCorrectTFReady {μ : Model V Tag} [bb : ThyBB μ] : ∀ p, ∀ v, p ⊨[μ] ⊡ₑ (TFₑ [ready, .val v]ₑ) := by
  intro p v
  have b := Lemmas.valid_forall.mp (bb.BrCorrect p) v
  simp only [substSimp] at b; replace b := Lemmas.valid_and.mp b |>.1
  rw [TF_all] at b
  simp [denotation] at b; obtain ⟨b1, b2, b3⟩ := b
  simp [denotation]; refine ⟨b1, b2, ?_⟩; intro x xb1
  exact b3 x xb1 v

theorem BrCorrectTFEcho {μ : Model V Tag} [bb : ThyBB μ] : ∀ p, ∀ v, p ⊨[μ] ⊡ₑ (TFₑ [echo, .val v]ₑ) := by
  intro p v
  have b := Lemmas.valid_forall.mp (bb.BrCorrect p) v
  simp only [substSimp] at b; replace b := Lemmas.valid_and.mp b |>.2
  rw [TF_all] at b
  simp [denotation] at b; obtain ⟨b1, b2, b3⟩ := b
  simp [denotation]; refine ⟨b1, b2, ?_⟩; intro x xb1
  exact b3 x xb1 v

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

end Lemma_4_2_6

namespace Lemma_4_2_8

variable
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {μ : Model V Tag}
  [bb : ThyBB μ]
  {v : V}

theorem t1 (h : ⊨[μ] □ₑ [echo, .val v]ₑ) : ⊨[μ] Tₑ (⊡ₑ [echo, .val v]ₑ) := by
  intro p
  have b := Lemmas.valid_forall.mp (bb.BrCorrect p) v
  simp only [substSimp] at b; replace b := Lemmas.valid_and.mp b |>.2
  rw [TF_all] at b
  simp [denotation] at b; obtain ⟨b1, b2, b3⟩ := b
  simp [denotation]; refine ⟨b1, b2, ?_⟩; intro x xb1
  have i := b3 x xb1 v; specialize h echo; simp [denotation] at h
  rw [Atom.Proposition_2_2_2.p8.mp h] at i; simp at i; assumption

theorem t2 (h : ⊨[μ] □ₑ [ready, .val v]ₑ) : ⊨[μ] Tₑ (⊡ₑ [ready, .val v]ₑ) := by
  intro p
  have b := Lemmas.valid_forall.mp (bb.BrCorrect p) v
  simp only [substSimp] at b; replace b := Lemmas.valid_and.mp b |>.1
  rw [TF_all] at b
  simp [denotation] at b; obtain ⟨b1, b2, b3⟩ := b
  simp [denotation]; refine ⟨b1, b2, ?_⟩; intro x xb1
  have i := b3 x xb1 v; specialize h echo; simp [denotation] at h
  rw [Atom.Proposition_2_2_2.p8.mp h] at i; simp at i; assumption

end Lemma_4_2_8

namespace Proposition_4_2_9

variable
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {μ : Model V Tag}
  [bb : ThyBB μ]
  {v : V}

theorem t : ⊨[μ] (◇ₑ [broadcast, .val v]ₑ →ₑ □ₑ [deliver, .val v]ₑ) := by
  intro p; rw [Lemmas.valid_impl]; intro h
  have h1 : ∀ p', ⟦◇ₑ [broadcast, .val v]ₑ⟧ᵈ μ p' = .true := by
    intro p'; rw [den_somewhere_global p p'] at h; rw [h]
  have h2 : ⊨[μ] □ₑ [echo, .val v]ₑ := by
    intro p'; apply Lemmas.valid_impl.mp (Lemma_4_2_6.t2 p') (h1 p')
  have h3 : ⊨[μ] Tₑ (⊡ₑ [echo, .val v]ₑ) := Lemma_4_2_8.t1 h2
  have h3' : ∀ p, ⟦⊡ₑ [echo, .val v]ₑ⟧ᵈ μ p = .true := by
    intro p; simpa using h3 p
  have h4 : ⊨[μ] □ₑ [ready, .val v]ₑ := by
    intro p'; exact Lemmas.valid_impl.mp (Lemma_4_2_6.t3 p') (h3' p')
  have h4 : ⊨[μ] Tₑ (⊡ₑ [ready, .val v]ₑ) := Lemma_4_2_8.t2 h4
  have h5 : ⊨[μ] □ₑ [deliver, .val v]ₑ := by
    intro p'; exact Lemmas.valid_impl.mp (Lemma_4_2_6.t4 p') (by simpa using h4 p')
  exact h5 p

end Proposition_4_2_9

-- NOTE: I dropped the assumption for S to be 3-Twined
namespace Lemma_4_2_10

variable
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {μ : Model V Tag}
  [bb : ThyBB μ]
  {v v' : V}
  {tag : Tag}

omit bb in
theorem taux1 (h : ⊨[μ] (⊡ₑ [tag, .val v]ₑ)) (t : ⊨[μ] (⊡ₑ (TFₑ [tag, .val v]ₑ)))
  : ∀ p, ⟦[tag, .val v ]ₑ⟧ᵈ μ p = .true := by
  intro p
  have l : ⊨[μ] (⟐ₑ (Tₑ [tag, .val v]ₑ)) := by
     intro p; simp [denotation]; intro x xm; constructor
     · simp [Open1, Finset.Nonempty] at xm; exact xm.2
     · specialize h p; specialize t p
       simp [denotation] at h t
       obtain ⟨h1, h2, h3⟩ := h; obtain ⟨t1, t2, t3⟩ := t
       simp [Open1, Finset.Nonempty] at h2 t2
       obtain ⟨_, hm⟩ := h2.2; obtain ⟨_, tm⟩ := t2.2
       have x1 := h3 _ hm; simp at x1
       have x2 := t3 _ tm; simp at x2
       apply Lemmas.valid_and_TF x1 x2
  simp [denotation]
  specialize l p; simp [denotation] at l
  have ll := l ?_ ?_
  exact ll.2
  exact Finset.univ; simp [Open1]; exact μ.S.univ_open

 theorem tauxReady (h : ⊨[μ] (⊡ₑ [ready, .val v]ₑ))
  : ∀ p, ⟦[ready, .val v ]ₑ⟧ᵈ μ p = .true := by
   intro p; apply taux1 h
   intro p; exact BrCorrectTFReady p v

 theorem tauxEcho (h : ⊨[μ] (⊡ₑ [echo, .val v]ₑ))
  : ∀ p, ⟦[echo, .val v ]ₑ⟧ᵈ μ p = .true := by
   intro p; apply taux1 h
   intro p; exact BrCorrectTFEcho p v

theorem t1 : (⊨[μ] ⊡ₑ [ready, .val v]ₑ) → ⊨[μ] Tₑ (⟐ₑ [ready, .val v]ₑ) := by
  intro h p; have a := tauxReady h p; simp [denotation] at a
  simp [denotation]; intro x x1; simp [Open1, Finset.Nonempty] at x1; constructor
  exact x1.2; assumption

theorem t2 (h : ⊨[μ] (⊡ₑ [echo, .val v]ₑ ∧ₑ ⊡ₑ [echo, .val v']ₑ))
  : ⊨[μ] (Tₑ (◇ₑ ([echo, .val v]ₑ ∧ₑ [echo, .val v']ₑ))) := by
  intro p
  have ⟨hv, hv'⟩ := Lemmas.valid_and.mp (h p)
  have tv := tauxEcho (quorum_global'.mp hv) p
  have tv' := tauxEcho (quorum_global'.mp hv') p; simp [denotation] at tv tv'
  simp [denotation, tv, tv']

theorem t3 (h : ⊨[μ] (⊡ₑ [ready, .val v]ₑ ∧ₑ ⊡ₑ [ready, .val v']ₑ))
  : ⊨[μ] (Tₑ (◇ₑ ([ready, .val v]ₑ ∧ₑ [ready, .val v']ₑ))) := by
  intro p
  have ⟨hv, hv'⟩ := Lemmas.valid_and.mp (h p)
  have tv := tauxReady (quorum_global'.mp hv) p
  have tv' := tauxReady (quorum_global'.mp hv') p; simp [denotation] at tv tv'
  simp [denotation, tv, tv']

end Lemma_4_2_10

namespace Proposition_4_2_11
variable
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {μ : Model V Tag}
  [bb : ThyBB μ]
  {v : V}

theorem t : ⊨[μ] ∃₀₁ₑ (◇ₑ [deliver]ₑ) := by
  intro p;
  simp only [valid_pred, Lemmas.denotation_exists_affine, substSimp, Lemmas.byzantine_le_affine_implies_eq]
  intro v1 v2 h1 h2; simp [denotation] at h1 h2
  have h {u} (tu : Model.ς μ deliver u = Three.true)
       : ⊨[μ] ⊡ₑ [ready, Term.val u]ₑ := by
    intro p'
    have g := Lemmas.valid_forall.mp (bb.BrDeliver? p) u; simp only [substSimp] at g
    rw [Lemmas.valid_impl, Lemmas.substAt_bound, Lemmas.denotation_predicate] at g
    exact quorum_global (g tu)
  have d1 := h h1; have d2 := h h2
  have mke {v} (x : Model.ς μ ready v = Three.true) : ⊨[μ] (⊡ₑ [echo, .val v]ₑ) := by
    intro p';
    have h := Lemmas.valid_forall.mp (bb.BrReady? p') v
    simp only [substSimp] at h; simp only [Lemmas.valid_impl] at h
    rw [Lemmas.substAt_bound] at h; simp only [denotation] at h
    exact h x
  have hr : ⊨[μ] (Tₑ (◇ₑ ([ready, .val v1]ₑ ∧ₑ [ready, .val v2]ₑ))) := by
    apply Lemma_4_2_10.t3; intro p
    apply Lemmas.valid_and.mpr
    exact ⟨d1 p, d2 p⟩
  have vready : (Model.ς μ ready v1 = Three.true) ∧ Model.ς μ ready v2 = Three.true := by
    specialize hr default
    simpa [denotation, Lemmas.and_true] using hr
  have he : ⊨[μ] (Tₑ (◇ₑ ([echo, .val v1]ₑ ∧ₑ [echo, .val v2]ₑ))) := by
    apply Lemma_4_2_10.t2; intro p
    apply Lemmas.valid_and.mpr
    refine ⟨mke vready.1 p, mke vready.2 p⟩
  have z := bb.BrEcho01 p
  rw [valid_pred, Lemmas.denotation_exists_affine] at z; simp only at z
  conv at z => right; right; ext v; simp [Lemmas.substAt_predicate, Lemmas.substAt_bound, denotation]
  specialize he p; simp [denotation, Lemmas.and_true] at he
  apply Lemmas.byzantine_le_affine_implies_eq.mp z he.1 he.2

end Proposition_4_2_11

end Modal_Logic
