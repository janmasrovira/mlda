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

-- The type Expr defined here corresponds to the sum of Terms and Predicates defined in the paper
inductive Expr (S P V : Type) : Nat → Type where
  | atom {n} : S → Term V n → Expr S P V n
  | bot {n} : Expr S P V n
  | neg {n} : Expr S P V n → Expr S P V n
  | and {n} : Expr S P V n → Expr S P V n → Expr S P V n
  | quorum {n} : Expr S P V n → Expr S P V n
  | everywhere {n} : Expr S P V n → Expr S P V n
  | tf {n} : Expr S P V n → Expr S P V n
  | t {n} : Expr S P V n → Expr S P V n
  | exist {n} : Expr S P V (n +1) → Expr S P V n
  | exist_affine {n} : Expr S P V (n +1) → Expr S P V n

def Interpretation (S P V : Type) := S → P → V → 𝟯

structure Model
  (Sig : Type)
  (P : Type) [Fintype P] [DecidableEq P] [Inhabited P]
  (V : Type) [Fintype V] [DecidableEq V] where
  S : FinSemitopology P
  ς : Interpretation Sig P V

end Types

namespace Notation

variable
  {S P V : Type}
  [Fintype V]
  [DecidableEq V]
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
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

abbrev somewhere (φ : Expr S P V n) : Expr S P V n := ¬ₑ (□ₑ (¬ₑ φ))
scoped notation "◇ₑ " => somewhere

abbrev contraquorum (φ : Expr S P V n) : Expr S P V n := ¬ₑ (⊡ₑ (¬ₑ φ))
scoped notation "⟐ₑ " => contraquorum

abbrev or {n : Nat} (φ ψ : Expr S P V n) : Expr S P V n := ¬ₑ (¬ₑ φ ∧ₑ ¬ₑ ψ)
scoped infixl:30 " ∨ₑ " => or

@[simp] def impl {n : Nat} (φ ψ : Expr S P V n) : Expr S P V n := ¬ₑ φ ∨ₑ ψ
scoped infixl:25 " →ₑ " => impl

abbrev for_all {n : Nat} (φ : Expr S P V (n +1)) : Expr S P V n := ¬ₑ (∃⁎ₑ (¬ₑ φ))
scoped notation "∀ₑ " => for_all

abbrev existence_unique {n : Nat} (φ : Expr S P V (n +1)) : Expr S P V n := ∃⁎ₑ φ ∧ₑ ∃₀₁ₑ φ
scoped notation "∃₁ₑ " => existence_unique

abbrev is_byzantine {n : Nat} (φ : Expr S P V n) : Expr S P V n := ¬ₑ (TFₑ φ)
scoped notation "Bₑ " => is_byzantine

scoped notation "[" s ", " t "]ₑ" => Expr.atom s t
scoped notation "[" s "]ₑ" => Expr.atom s (Term.bound 0)

abbrev TF_all {n : Nat} (s : S) : Expr S P V n := ∀ₑ (TFₑ [s]ₑ)
scoped notation "TF[" s "]ₑ" => TF_all s

abbrev B_all {n : Nat} (s : S) : Expr S P V n := ∀ₑ (Bₑ [s]ₑ)
scoped notation "B[" s "]ₑ" => B_all s

end Notation

open Notation

namespace Denotation

open scoped FinSemitopology

variable
  {S P V : Type}
  [Fintype V]
  [DecidableEq V]
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  (μ : Model S P V)

@[simp] abbrev Term.substAt {n : Nat} (k : Fin (n + 1)) (v : V) (t : Term V (n + 1)) : Term V n :=
  match t with
  | .val w => .val w
  | .bound i =>
    if h : i = k then .val v
    else if h : i < k then .bound ⟨i, by omega⟩
    else .bound ⟨i - 1, by omega⟩

@[simp] def substAt {n : Nat} (k : Fin (n + 1)) (v : V) : Expr S P V (n + 1) → Expr S P V n
  | .bot           => .bot
  | .neg e         => .neg (substAt k v e)
  | .and l r       => .and (substAt k v l) (substAt k v r)
  | .quorum e      => .quorum (substAt k v e)
  | .everywhere e  => .everywhere (substAt k v e)
  | .tf e          => .tf (substAt k v e)
  | .t e           => .t (substAt k v e)
  | .atom p t      => .atom p (Term.substAt k v t)
  | .exist e       => .exist (substAt k.succ v e)
  | .exist_affine e => .exist_affine (substAt k.succ v e)

def Expr.size {n : Nat} : Expr S P V n → Nat
  | .bot | .atom _ _ => 0
  | .and l r => Expr.size l + Expr.size r +1
  | .neg e | .quorum e | .everywhere e | .tf e | .t e | .exist e | .exist_affine e => Expr.size e +1

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Inhabited P] in
theorem substAt_size {n : Nat} (k : Fin (n + 1)) (v : V) (φ : Expr S P V (n + 1)) :
  Expr.size (substAt k v φ) = Expr.size φ :=
  match φ with
  | .bot => by simp [Expr.size, substAt]
  | .neg e => by simp [Expr.size, substAt, substAt_size k v e]
  | .tf e => by simp [Expr.size, substAt, substAt_size k v e]
  | .quorum e => by simp [Expr.size, substAt, substAt_size k v e]
  | .atom p t => by simp [Expr.size, substAt]
  | .t e => by simp [Expr.size, substAt, substAt_size k v e]
  | .everywhere e => by simp [Expr.size, substAt, substAt_size k v e]
  | .and l r => by simp [Expr.size, substAt, substAt_size k v l, substAt_size k v r]
  | .exist e => by simp [Expr.size, substAt, substAt_size (n := n + 1) k.succ v e]
  | .exist_affine e => by simp [Expr.size, substAt, substAt_size (n := n + 1) k.succ v e]

def denotation (φ : Expr S P V 0) (p : P) : 𝟯 :=
  let denTerm (s : S) (p' : P) (t : Term V 0) : 𝟯 := match t with
    | .val v => μ.ς s p' v
  match φ, h : Expr.size φ with
  | .bot, _ => .false
  | .and l r, _ => denotation l p ∧ denotation r p
  | .tf e, _ => TF (denotation e p)
  | .t e, _ => T (denotation e p)
  | .neg e, _ => ¬ (denotation e p)
  | .quorum e, _ => ⊡(μ.S) (fun p => denotation e p)
  | .everywhere e, _ => □ (fun p => denotation e p)
  | .atom p' t, _ => denTerm p' p t
  | .exist e, _ => ∃⁎ (fun v => denotation (substAt 0 v e) p)
  | .exist_affine e, _ => ∃₀₁ (fun v => denotation (substAt 0 v e) p)
  termination_by Expr.size φ
  decreasing_by all_goals try simp [Expr.size, substAt_size] <;> omega

scoped notation  "ₛ[" φ ", " ix "↦" v "]" => substAt ix v φ
scoped notation "⟦" φ' "⟧ᵈ" => denotation (φ := φ')

abbrev valid_pred (p : P) (φ : Expr S P V 0) : Prop := .byzantine ≤ ⟦ φ ⟧ᵈ μ p
abbrev valid (φ : Expr S P V 0) := ∀ p, valid_pred μ p φ

scoped notation p " ⊨[" μ "] " φ => valid_pred μ p φ
scoped notation "⊨[" μ "] " φ => valid μ φ

end Denotation

open Denotation

section Notation_3_2_4

variable
  {V P S : Type}
  [Fintype V]
  [DecidableEq V]
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  {μ : Model S P V}
  {p p' : P}
  {φ : Expr S P V 0}

theorem den_somewhere_global (p p' : P) : ⟦◇ₑ φ⟧ᵈ μ p = ⟦◇ₑ φ⟧ᵈ μ p' := by simp [denotation]
theorem somewhere_global : (p ⊨[μ] (◇ₑ φ)) → p' ⊨[μ] (◇ₑ φ) := by simp [den_somewhere_global p p']

theorem den_everywhere_global (p p' : P) : ⟦□ₑ φ⟧ᵈ μ p = ⟦□ₑ φ⟧ᵈ μ p' := by simp [denotation]
theorem everywhere_global : (p ⊨[μ] (□ₑ φ)) → p' ⊨[μ] (□ₑ φ) := by simp [den_everywhere_global p p']

theorem valid_iff_everywhere : (⊨[μ] φ) ↔ p ⊨[μ] (□ₑ φ) := by
  simp [valid, denotation]
theorem valid_iff_everywhere' : (⊨[μ] φ) ↔ p ⊨[μ] (□ₑ φ) := by
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
  {S P V : Type}
  [Fintype V]
  [DecidableEq V]
  [Fintype P]
  [DecidableEq P]
  [Inhabited P]
  {μ : Model S P V}
  {s : S}
  {p p' : P}
  {n : Nat}
  {k : Fin (n + 1)}
  {v : V}
  {φ ψ : Expr S P V 0}
  {α β : Expr S P V (n + 1)}
  {φ₁ : Expr S P V 1}
  {Γ : List.Vector V n}

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Inhabited P] in
@[substSimp] theorem substAt_impl : ₛ[α →ₑ β, k ↦ v] = (ₛ[α, k ↦ v] →ₑ ₛ[β, k ↦ v]) := by simp

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Inhabited P] in
@[substSimp] theorem substAt_or : ₛ[α ∨ₑ β, k ↦ v] = (ₛ[α, k ↦ v] ∨ₑ ₛ[β, k ↦ v]) := by simp

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Inhabited P] in
@[substSimp] theorem substAt_and : ₛ[α ∧ₑ β, k ↦ v] = (ₛ[α, k ↦ v] ∧ₑ ₛ[β, k ↦ v]) := by simp

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Inhabited P] in
@[substSimp] theorem substAt_tf : ₛ[TFₑ α, k ↦ v] = TFₑ ₛ[α, k ↦ v] := by simp

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Inhabited P] in
@[substSimp] theorem substAt_tf_all : ₛ[TF[s]ₑ, k ↦ v] = (TF[s]ₑ : Expr S P V n) := by
  simp; intro q; exact absurd q (Fin.succ_ne_zero k).symm

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Inhabited P] in
@[substSimp] theorem substAt_somewhere : ₛ[◇ₑ α, k ↦ v] = (◇ₑ ₛ[α, k ↦ v]) := by simp

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Inhabited P] in
@[substSimp] theorem substAt_quorum : ₛ[⊡ₑ α, k ↦ v] = (⊡ₑ ₛ[α, k ↦ v]) := by simp

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Inhabited P] in
@[substSimp] theorem substAt_exists {n} {k : Fin (n + 1)} {α : Expr S P V (n + 2)} :
  ₛ[∃⁎ₑ α, k ↦ v] = ∃⁎ₑ ₛ[α, k.succ ↦ v] := by simp

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Inhabited P] in
@[substSimp] theorem substAt_atom {t : Term V (n +1)}
  : ₛ[[ s, t]ₑ, k ↦ v] = ([s, Term.substAt k v t]ₑ : Expr S P V _) := by simp [substAt]

omit [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] [Inhabited P] in
@[substSimp] theorem substAt_bound {n : Nat} : Term.substAt (n := n) 0 v (.bound 0) = .val (scope := n) v := by simp

@[simp] theorem denotation_neg : ⟦¬ₑ φ⟧ᵈ μ p = (¬ ⟦φ⟧ᵈ μ p) := by
  simp [denotation]

@[simp] theorem denotation_or : ⟦φ ∨ₑ ψ⟧ᵈ μ p = (⟦φ⟧ᵈ μ p ∨ ⟦ψ⟧ᵈ μ p) := by
  simp [denotation]

theorem denotation_impl : ⟦φ →ₑ ψ⟧ᵈ μ p = (⟦φ⟧ᵈ μ p → ⟦ψ⟧ᵈ μ p) := by
  simp [denotation, Three.Atom.impl, Lemmas.neg_and]

theorem denotation_true : ⟦Tₑ φ⟧ᵈ μ p = T (⟦φ⟧ᵈ μ p) := by
  simp [denotation]

theorem denotation_everywhere : ⟦□ₑ φ⟧ᵈ μ p = □ (fun p => ⟦φ⟧ᵈ μ p) := by
  simp [denotation]

theorem denotation_somewhere : ⟦◇ₑ φ⟧ᵈ μ p = ◇ (fun p => ⟦φ⟧ᵈ μ p) := by
  simp [denotation, ← Lemmas.join_neg]; congr; ext k; simp

theorem denotation_quorum : ⟦⊡ₑ φ⟧ᵈ μ p = ⊡(μ.S) (fun p => ⟦φ⟧ᵈ μ p) := by
  simp [denotation]

theorem denotation_contraquorum : ⟦⟐ₑ φ⟧ᵈ μ p = ⟐(μ.S) (fun p => ⟦φ⟧ᵈ μ p) := by
  simp [denotation, FinSemitopology.contraquorum, FinSemitopology.quorum, ← Lemmas.meet_neg]
  congr; ext k; simp [← Lemmas.join_neg, Function.neg]
  congr 1; ext _; simp

theorem denotation_atom : ⟦[s, .val v]ₑ⟧ᵈ μ p = μ.ς s p v  := by
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
