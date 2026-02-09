-- NOTE the name of this file is temporary. Eventually code in this file will be reorganized

import mlda.Base
import mlda.Three
import mlda.FinSemitopology

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

abbrev existence : 𝟯 := allValues |>.fold max false f
scoped notation " ∃⁎ " => existence

abbrev existence_affine : 𝟯 := allValues |>.fold min true (and_implies_eq_all f)
scoped notation " ∃₀₁ " => existence_affine

abbrev existence_unique : 𝟯 := existence f ∧ existence_affine f
scoped notation " ∃₁ " => existence_unique

end Definitions

open Definitions

namespace Lemmas

open scoped Three.Atom

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
   simpa using Three.Lemmas.mp_weak (h v v') (Three.Lemmas.le_and.mpr ⟨vt, vt'⟩)

theorem unique_implies_existence_affine : a ≤ ∃₁ f → (a ≤ ∃⁎ f) ∧ (a ≤ ∃₀₁ f) := by
  intro h; simp [existence_unique] at h
  exact Three.Lemmas.le_and.mp h

theorem unique_implies_affine : a ≤ ∃₁ f → a ≤ ∃₀₁ f := by
  intro h; exact unique_implies_existence_affine h |>.2

theorem unique_implies_existence : a ≤ ∃₁ f → a ≤ ∃⁎ f := by
  intro h; exact unique_implies_existence_affine h |>.1

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
  exists v'; simpa [v1, v2]

theorem t2 : (∃! v, f v = .true) → (∀ v', f v' ≠ .byzantine) → ∃₁ f = .true := by
  rintro ⟨t, ft, h1⟩ h2
  simp [existence_unique, Three.Lemmas.and_true]; constructor
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
      cases fx : f x <;> cases fy : f y <;> first | contradiction | simp <;> try exact ne_or_eq x y
      have := p x; rw [fx] at this; contradiction
    · exists v; simp [fv]
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
    constructor <;> assumption
  · intro ⟨h1, h2⟩
    rw [existence_unique]
    apply Three.Lemmas.le_and.mpr
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
    simp [Three.Lemmas.impl_true]; intro x y p
    obtain ⟨h1, h2⟩ := Three.Lemmas.le_and.mp p
    apply_rules [p]

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

namespace Part_5

theorem t (h1 : (⊨ (∃₀₁ f) ∨ ⊨ (∃₁ f))) (h2 : ⊨ (T (f v ∧ f v'))) : v = v' := by
  simp at h1 h2
  obtain ⟨fv, fv'⟩ := Three.Lemmas.and_true.mp h2
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

abbrev TF_all {n : Nat} (p : P) : Expr V P n := ∀ₑ (TFₑ [p]ₑ)
scoped notation "TF[" p "]ₑ" => TF_all p

abbrev B_all {n : Nat} (p : P) : Expr V P n := ∀ₑ (Bₑ [p]ₑ)
scoped notation "B[" p "]ₑ" => B_all p

end Notation

open Notation

namespace Denotation

open scoped Three.Atom
open scoped FinSemitopology

variable
  {V P : Type}
  [Fintype V]
  [DecidableEq V]
  [Fintype P]
  [DecidableEq P]
  [Nonempty P]
  (μ : Model V P)

def go {n : Nat} (Γ : List.Vector V n) (φ : Expr V P n) (p : P) : 𝟯 :=
  let goTerm (p' : P) (t : Term V n) : 𝟯 := match t with
      | .bound a => μ.ς p' (Γ.get a)
      | .val v => μ.ς p' v
  match φ with
  | .bot => .false
  | .and l r => go Γ l p ∧ go Γ r p
  | .tf e => TF (go Γ e p)
  | .t e => T (go Γ e p)
  | .neg e => ¬ (go Γ e p)
  | .quorum e => ⊡(μ.S) (fun p => go Γ e p)
  | .everywhere e => □ (fun p => go Γ e p)
  | .predicate p t => goTerm p t
  | .term t => goTerm p t
  | .exist e => ∃⁎ (fun v => go (n := n +1) (v ::ᵥ Γ) e p)
  | .exist_affine e => ∃₀₁ (fun v => go (n := n +1) (v ::ᵥ Γ) e p)

def denotation (φ : Expr V P 0) (p : P) : 𝟯 := go μ .nil φ p

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

namespace Lemmas

open scoped FinSemitopology
open scoped Three.Atom
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
  {φ ψ : Expr V P 0}
 
@[simp] theorem valid_pred_or : (p ⊨[μ] φ ∨ₑ ψ) ↔ (p ⊨[μ] φ) ∨ p ⊨[μ] ψ := by
  simp [denotation, go, Three.Lemmas.le_or]

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
  -- [Nonempty V]
  [DecidableEq V]
  (μ : Model V Tag)
  -- [twined : FinSemitopology.Twined3 μ.S]
  [bb : ThyBB μ]

open scoped Three.Atom

abbrev P1 := (∀ p, p ⊨[μ] TF[.broadcast]ₑ) ∧ 
         ∃! v : V, ∀ p, p ⊨[μ] (Tₑ (◇ₑ [broadcast, .val v]ₑ))  

abbrev P2 := ∀ v, ∀ p, p ⊨[μ] Bₑ [broadcast, .val v]ₑ

theorem t : P1 μ ∨ P2 μ := by
  simp [P1, P2]
  cases Lemmas.valid_pred_or.mp (bb.BrCorrectBroadcast default)
  · next h => left; constructor
              · intro p; simp [denotation, go, existence] at *; intro v; 
                simp [Three.Lemmas.byzantine_le_TF]
                intro x; have k := Three.Lemmas.byzantine_le_TF.mp (h v)
                contradiction
              · have b := bb.BrBroadast1 default
                simp [denotation, go, existence, Three.Lemmas.le_and] at b
                have ⟨⟨v, b1⟩, b2⟩ := b; clear b
                exists v; simp [denotation, go] at h ⊢;
                have : Model.ς μ broadcast v = Three.true := by
                  specialize h v; simp [Three.Lemmas.byzantine_le_TF] at h
                  cases Three.Lemmas.byzantine_le.mp b1; contradiction; assumption
                constructor
                · assumption
                · intro u fx; specialize b2 u v; apply_rules
  · next h => right; intro v p; simp [denotation, go]; 
              simp [denotation, go, FinSemitopology.everywhere, existence] at h
              exact h v


end Lemma_4_2_4

end Modal_Logic
