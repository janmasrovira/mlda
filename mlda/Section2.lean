import mlda.Base

/-!
# Section 2: Three-valued logic and semitopologies

This file defines:

- **Three-valued logic** (`Three`, denoted as `𝟯`) and its operations
- **Fold operations**: `⋀` and `⋁` for big conjunction / disjunction over finsets.
- **Finite semitopologies** (`FinSemitopology`): a topology on a finite set of
  participants, equipped with modal operators `□` (everywhere), `◇` (somewhere),
  `⊡` (quorum), and `⟐` (contraquorum).
- **Twined semitopologies** (`Twined3`): the three-way intersection property
  guaranteeing that any three non-empty open sets share a common element.
-/

#eval IO.println "Checking definitions and proofs in Section 2..."

section Defeinition_2_2_1

inductive Three : Type where
  | Three_f
  | Three_b
  | Three_t

notation "𝟯" => Three
notation "𝐟" => Three.Three_f
notation "𝐛" => Three.Three_b
notation "𝐭" => Three.Three_t

end Defeinition_2_2_1

namespace Three

namespace Atom

variable
  {X : Type}

def neg : 𝟯 → 𝟯
  | 𝐟 => 𝐭
  | 𝐛 => 𝐛
  | 𝐭 => 𝐟
scoped prefix:75 "¬ " => neg

def and : 𝟯 → 𝟯 → 𝟯
  | 𝐭, 𝐭 => 𝐭
  | 𝐛, 𝐭 => 𝐛
  | 𝐭, 𝐛 => 𝐛
  | 𝐛, 𝐛 => 𝐛
  | _, _ => 𝐟

scoped infixl:35 " ∧ " => and

instance : Std.Associative and where
  assoc := by intro a b c; cases a <;> cases b <;> cases c <;> simp!

instance : Std.Commutative and where
  comm := by intro a b; cases a <;> cases b <;> simp!

instance : Std.LawfulCommIdentity and 𝐭 where
  left_id := by intro a; cases a <;> simp!

def or : 𝟯 → 𝟯 → 𝟯
  | 𝐟, 𝐟 => 𝐟
  | 𝐟, 𝐛 => 𝐛
  | 𝐛, 𝐟 => 𝐛
  | 𝐛, 𝐛 => 𝐛
  | _, _ => 𝐭

scoped infixl:30 " ∨ " => or

instance : Std.Associative or where
  assoc := by intro a b c; cases a <;> cases b <;> cases c <;> simp!

instance : Std.Commutative or where
  comm := by intro a b; cases a <;> cases b <;> simp!

instance : Std.LawfulCommIdentity or 𝐟 where
  left_id := by intro a; cases a <;> simp!

def xor : 𝟯 → 𝟯 → 𝟯
  | 𝐛, _ => 𝐛
  | _, 𝐛 => 𝐛
  | 𝐭, 𝐭 => 𝐟
  | 𝐟, 𝐟 => 𝐟
  | _, _ => 𝐭
scoped infixl:30 " ⊕ " => xor

@[simp] abbrev impl (a b : 𝟯) : 𝟯 := (¬ a) ∨ b
scoped infixl:25 " → " => impl

def isTrue : 𝟯 → 𝟯
 | 𝐭 => 𝐭
 | _ => 𝐟
scoped notation "T" => isTrue

def isByzantine : 𝟯 → 𝟯
 | 𝐛 => 𝐭
 | _ => 𝐟
scoped notation "B" => isByzantine

def isFalse : 𝟯 → 𝟯
 | 𝐟 => 𝐭
 | _ => 𝐟
scoped notation "F" => isFalse

def isNotFalse : 𝟯 → 𝟯
 | 𝐟 => 𝐟
 | _ => 𝐭
scoped notation "TB" => isNotFalse

def isNotByzantine : 𝟯 → 𝟯
 | 𝐛 => 𝐟
 | _ => 𝐭
scoped notation "TF" => isNotByzantine

def strongImpl : 𝟯 → 𝟯 → 𝟯
 | 𝐟, _ => 𝐭
 | 𝐛, 𝐭 => 𝐭
 | 𝐛, _ => 𝐛
 | 𝐭, 𝐭 => 𝐭
 | 𝐭, _ => 𝐟
scoped infixl:25 " ⇀ " => strongImpl

instance : Ord 𝟯 where
  compare := fun
   | 𝐟, 𝐟 => .eq
   | 𝐟, _ => .lt
   | _, 𝐟 => .gt
   | 𝐛, 𝐛 => .eq
   | 𝐛, 𝐭 => .lt
   | 𝐭, 𝐛 => .gt
   | 𝐭, 𝐭 => .eq

instance : Max Three where
  max := or

instance : Min Three where
  min := and

instance : LinearOrder Three := by
  let toFin : 𝟯 → Fin 3
    | 𝐟 => 0
    | 𝐛 => 1
    | 𝐭 => 2
  apply LinearOrder.liftWithOrd toFin
  intro x y p; cases x <;> cases y <;> cases p <;> rfl
  repeat (intro x y; cases x <;> cases y <;> rfl)

instance : BoundedOrder Three where
  bot := 𝐟
  bot_le := by intro a; cases a <;> decide
  top := 𝐭
  le_top := by intro a; cases a <;> decide

instance : DistribLattice Three where
  le_sup_inf := by intro a b c; cases a <;> cases b <;> cases c <;> decide

abbrev Valid (p : 𝟯) : Prop := 𝐛 ≤ p
scoped notation "⊨" => Valid

abbrev NotValid (p : 𝟯) : Prop := p = 𝐟
scoped notation "⊭" => NotValid

namespace Proposition_2_2_3

variable {a b : 𝟯}

@[simp] theorem p1_1 : ⊨ 𝐭 := by decide
@[simp] theorem p1_2 : ⊨ 𝐛 := by decide
@[simp] theorem p1_3 : ⊭ 𝐟 := by rfl
@[simp] theorem p1_4 : ¬ (⊨ 𝐟) := by intro k; cases k
@[simp] theorem p1_5 : ¬ (⊭ 𝐭) := by intro k; cases k
@[simp] theorem p1_6 : ¬ (⊭ 𝐛) := by intro k; cases k

theorem p2_1 : ⊨ (a ∨ b) ↔ ⊨ a ∨ ⊨ b := by
  constructor <;> intro x
  next => cases a <;> cases b <;> cases x <;> simp
  next => cases x <;> rename_i k <;> cases a <;> cases b <;> cases k <;> simp!

theorem p2_2 : ⊨ (a ∧ b) ↔ ⊨ a ∧ ⊨ b := by
  constructor <;> intro x
  next => cases a <;> cases b <;> cases x <;> simp
  next => rcases x with ⟨k1, k2⟩; cases a <;> cases b <;> cases k1 <;> cases k2 <;> simp!

theorem p3_1 : (a → b) = (¬ a ∨ b) := by rfl
theorem p3_2 : (a ⇀ b) = (a → T b) := by cases a <;> cases b <;> rfl

theorem p4 : ⊨ (a → b) ↔ ((a = 𝐭) → ⊨ (TB b)) := by
  cases a <;> cases b <;> simp [impl, or, neg, isNotFalse]

theorem p5 : ⊨ (a ⇀ b) ↔ ((a = 𝐭) → (b = 𝐭)) := by
  cases a <;> cases b <;> simp [strongImpl]

theorem p6 : ⊨ (a ∨ ¬ a) := by cases a <;> simp!

theorem p7 : ⊨ (a ∧ ¬ a) ↔ a = 𝐛 := by
  constructor <;> cases a <;> simp!

theorem p8 : ⊨ a ↔ (TF a = T a) := by cases a <;> simp!

theorem p9 : a ≤ b ↔ ((¬ b) ≤ ¬ a) := by
  constructor <;> cases a <;> cases b <;> decide

end Proposition_2_2_3

end Atom

namespace Function

open scoped Three.Atom

variable {X : Type}

abbrev bigAnd (P : Finset X) (f : X → 𝟯) : 𝟯 := P.fold min 𝐭 f
scoped notation "⋀" => bigAnd

abbrev bigOr (P : Finset X) (f : X → 𝟯) : 𝟯 := P.fold max 𝐟 f
scoped notation "⋁" => bigOr

@[simp] def lift2 (op : 𝟯 → 𝟯 → 𝟯) (f f' : X → 𝟯) : X → 𝟯 := fun x => op (f x) (f' x)

abbrev neg (f : X → 𝟯) : X → 𝟯 := Atom.neg ∘ f
scoped prefix:75 "¬" => neg

theorem neg_fold {f : X → 𝟯} : (fun x => ¬ (f x)) = (¬ f) := by rfl

def and (f f' : X → 𝟯) : X → 𝟯 := lift2 Atom.and f f'
scoped infixl:35 " ∧ " => and

def or (f f' : X → 𝟯) : X → 𝟯 := lift2 Atom.or f f'
scoped infixl:30 " ∨ " => or

def impl (f f' : X → 𝟯) : X → 𝟯 := lift2 Atom.impl f f'
def strongImpl (f f' : X → 𝟯) : X → 𝟯 := lift2 Atom.strongImpl f f'

end Function

namespace Lemmas

open scoped Three.Function
open Three.Function
open Three.Atom

variable
  {X : Type}
  {P : Finset X}
  {a b c : 𝟯}
  {f f' : X → 𝟯}

@[simp] theorem T_true : T a = 𝐭 ↔ a = 𝐭 := by cases a <;> decide

theorem false_or_byzantine_le : (a = 𝐟) ∨ 𝐛 ≤ a := by cases a <;> decide

theorem true_or_le_byzantine : (a = 𝐭) ∨ a ≤ 𝐛 := by cases a <;> decide

@[simp] theorem and_idempotent : (a ∧ a) = a := by cases a <;> simp!

@[simp] theorem or_idempotent : (a ∨ a) = a := by cases a <;> simp!

@[simp] theorem Function.and_idempotent : (f ∧ f) = f := by funext a; simp [Function.and]

@[simp] theorem Function.or_idempotent : (f ∨ f) = f := by funext a; simp [Function.or]

theorem neg_or : (¬ (a ∨ b)) = (¬ a ∧ ¬ b) := by
  cases a <;> cases b <;> simp!

theorem neg_and : (¬ (a ∧ b)) = (¬ a ∨ ¬ b) := by
  cases a <;> cases b <;> simp!

@[simp] theorem Function.and_applied {x} : (f ∧ f') x = (f x ∧ f' x) := by
  simp [Function.and]

@[simp] theorem Function.neg_applied {x} : (¬ f) x = ¬ (f x) := by simp [Function.neg]

theorem Function.neg_and : (¬ (f ∧ f')) = (¬ f ∨ ¬ f') := by
  rw [Three.Function.and, Three.Function.or, Three.Function.neg]
  funext; apply Lemmas.neg_and

@[simp] theorem neg_neg : (¬ ¬ a) = a := by
  cases a <;> rfl

@[simp] theorem Function.neg_neg : (¬ (¬ f)) = f := by
  unfold Three.Function.neg; funext a; rw [Function.comp, Function.comp]
  cases h : f a <;> rfl

@[simp] theorem byzantine_le_neg : 𝐛 ≤ ¬ a ↔ a ≤ 𝐛 := by
  cases a <;> decide

theorem le_or : c ≤ (a ∨ b) ↔ (c ≤ a ∨ c ≤ b) := by
  cases a <;> cases b <;> cases c <;> decide

theorem or_le : (a ∨ b) ≤ c ↔ (a ≤ c ∧ b ≤ c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem le_and : c ≤ (a ∧ b) ↔ (c ≤ a ∧ c ≤ b) := by
  cases a <;> cases b <;> cases c <;> decide

theorem and_le : (a ∧ b) ≤ c ↔ (a ≤ c ∨ b ≤ c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem and_true : (a ∧ b) = 𝐭 ↔ (a = 𝐭 ∧ b = 𝐭) := by
  cases a <;> cases b <;> decide

theorem and_byzantine : (a ∧ b) = 𝐛 ↔ (a = 𝐛 ∧ 𝐛 ≤ b) ∨ (b = 𝐛 ∧ 𝐛 ≤ a) := by
  cases a <;> cases b <;> decide

theorem byzantine_le_and : 𝐛 ≤ (a ∧ b) ↔ (𝐛 ≤ a ∧ 𝐛 ≤ b) := by
  cases a <;> cases b <;> decide

theorem and_false : (a ∧ b) = 𝐟 ↔ (a = 𝐟 ∨ b = 𝐟) := by
  cases a <;> cases b <;> decide

theorem or_true : (a ∨ b) = 𝐭 ↔ (a = 𝐭 ∨ b = 𝐭) := by
  cases a <;> cases b <;> decide

theorem impl_true : (a → b) = 𝐭 ↔ (𝐛 ≤ a → b = 𝐭) := by
  cases a <;> cases b <;> decide

theorem impl_byzantine : (a → b) = 𝐛 ↔
    (a ≤ 𝐛 ∨ b ≠ 𝐛) → (a = 𝐛 ∧ b ≤ 𝐛) := by
  cases a <;> cases b <;> decide

@[simp] theorem bot_le : 𝐟 ≤ a ↔ True := by
  cases a <;> decide

@[simp] theorem le_bot : a ≤ 𝐟 ↔ a = 𝐟 := by
  cases a <;> decide

@[simp] theorem false_lt : 𝐟 < a ↔ 𝐛 ≤ a := by
  cases a <;> decide

@[simp] theorem lt_true : a < 𝐭 ↔ a ≤ 𝐛 := by
  cases a <;> decide

@[simp] theorem top_le : 𝐭 ≤ a ↔ a = 𝐭 := by
  cases a <;> decide

@[simp] theorem le_top : a ≤ 𝐭 ↔ True := by
  cases a <;> decide

theorem byzantine_le : 𝐛 ≤ a ↔ a = 𝐛 ∨ a = 𝐭 := by
  cases a <;> decide

theorem le_byzantine : a ≤ 𝐛 ↔ a = 𝐟 ∨ a = 𝐛 := by
  cases a <;> decide

theorem le_helper (p : 𝐛 ≤ a → b ≤ 𝐛 → a ≤ b) : a ≤ b := by
  cases a <;> cases b <;> try decide
  repeat (simp at p)

theorem le_by_cases (c1 : a = 𝐭 → b ≤ 𝐛 → b = 𝐭)
                    (c2 : a = 𝐛 → b ≤ 𝐛 → 𝐛 ≤ b)
 : a ≤ b := by
  cases a <;> cases b <;> try decide
  repeat (simp at c1 c2)

@[simp] theorem meet_false : ⋀ P f = 𝐟 ↔ ∃ x ∈ P, f x = 𝐟 := by
  unfold bigAnd;
  have h : P.fold min 𝐭 f ≤ 𝐟 ↔ _ ∨ ∃ x ∈ P, f x ≤ 𝐟 :=
    Finset.fold_min_le 𝐟
  simpa using h

@[simp] theorem meet_byzantine : P.fold min 𝐭 f = 𝐛 ↔ (∀ x ∈ P, 𝐛 ≤ f x) ∧ ∃ x ∈ P, f x = 𝐛 := by
  have h1 : P.fold min 𝐭 f ≤ 𝐛 ↔ _ ∨ ∃ x ∈ P, f x ≤ 𝐛 :=
    Finset.fold_min_le 𝐛
  have h2 : 𝐛 ≤ P.fold min 𝐭 f ↔ _ ∧ ∀ x ∈ P, 𝐛 ≤ f x :=
    Finset.le_fold_min 𝐛
  generalize P.fold Atom.and 𝐭 f = y at *
  constructor
  intro x; rw [x] at h1 h2; simp at h1 h2;
  constructor; assumption; rcases h1 with ⟨p1, p2, p3⟩; exists p1; constructor; assumption
  apply le_antisymm; assumption; apply h2; assumption
  rintro ⟨a, b⟩; apply le_antisymm; apply h1.mpr; simp; rcases b with ⟨p1, p2, p3⟩;
  exists p1; constructor; assumption; exact ge_of_eq p3.symm
  apply h2.mpr; simp; assumption

@[simp] theorem meet_true : P.fold min 𝐭 f = 𝐭 ↔ ∀ x ∈ P, f x = 𝐭 := by
  have h : 𝐭 ≤ P.fold min 𝐭 f ↔ _ ∧ ∀ x ∈ P, 𝐭 ≤ f x :=
    Finset.le_fold_min 𝐭
  simpa using h

@[simp] theorem join_false : ⋁ P f = 𝐟 ↔ ∀ x ∈ P, f x = 𝐟 := by
  unfold bigOr;
  have h : P.fold max 𝐟 f ≤ 𝐟 ↔ _ ∧ ∀ x ∈ P, f x ≤ 𝐟 :=
    Finset.fold_max_le 𝐟
  simpa using h

@[simp] theorem join_le_byzantine : P.fold max 𝐟 f ≤ 𝐛 ↔ (∀ x ∈ P, f x ≤ 𝐛) := by
  have h1 : P.fold max 𝐟 f ≤ 𝐛 ↔ _ ∧ ∀ x ∈ P, f x ≤ 𝐛 :=
    Finset.fold_max_le 𝐛
  simpa using h1

@[simp] theorem byzantine_le_meet : 𝐛 ≤ P.fold min 𝐭 f ↔ ∀ x ∈ P, f x ≥ 𝐛 := by
  have h2 : 𝐛 ≤ P.fold min 𝐭 f ↔ _ ∧ ∀ x ∈ P, 𝐛 ≤ f x :=
    Finset.le_fold_min (f := f) 𝐛
  simpa using h2

@[simp] theorem byzantine_le_join : 𝐛 ≤ P.fold max 𝐟 f ↔ ∃ x ∈ P, f x ≥ 𝐛 := by
  have h2 : 𝐛 ≤ P.fold max 𝐟 f ↔ _ ∨ ∃ x ∈ P, f x ≥ 𝐛 :=
    Finset.le_fold_max 𝐛
  simpa using h2

theorem le_meet : a ≤ ⋀ P f ↔ ∀ x ∈ P, a ≤ f x := by
  simpa using (Finset.le_fold_min (b := 𝐭) a)

theorem meet_le : ⋀ P f ≤ a ↔ a = 𝐭 ∨ ∃ x ∈ P, f x ≤ a := by
  simpa using (Finset.fold_min_le (b := 𝐭) a)

@[simp] theorem meet_le_byzantine : P.fold min 𝐭 f ≤ 𝐛 ↔ (∃ x ∈ P, f x ≤ 𝐛) := by
  simp [meet_le]


theorem le_join : a ≤ P.fold max 𝐟 f ↔ a = 𝐟 ∨ ∃ x ∈ P, f x ≥ a := by
  simpa using (Finset.le_fold_max (b := 𝐟) a)

theorem join_le : ⋁ P f ≤ a ↔ ∀ x ∈ P, f x ≤ a := by
  simpa using (Finset.fold_max_le (b := 𝐟) a)

theorem join_byzantine : P.fold max 𝐟 f = 𝐛 ↔ (∀ x ∈ P, f x ≤ 𝐛) ∧ ∃ x ∈ P, f x = 𝐛 := by
  constructor
  · intro h
    obtain ⟨u, um, up⟩ := byzantine_le_join.mp (ge_of_eq h)
    have h2 := join_le_byzantine.mp (le_of_eq h)
    constructor; assumption
    refine ⟨u, um, ?_⟩
    exact le_antisymm (h2 u um) up
  · rintro ⟨h1, u, um, up⟩
    apply le_antisymm
    apply join_le_byzantine.mpr; assumption
    apply byzantine_le_join.mpr
    refine ⟨u, um, ge_of_eq up⟩

@[simp] theorem join_true : ⋁ P f = 𝐭 ↔ ∃ x ∈ P, f x = 𝐭 := by
  unfold bigOr;
  have h : 𝐭 ≤ P.fold max 𝐟 f ↔ _ ∨ ∃ x ∈ P, 𝐭 ≤ f x :=
    Finset.le_fold_max 𝐭
  simpa using h

theorem meet_neg : ⋀ P (Atom.neg ∘ f) = ¬ ⋁ P f := by
  have := Finset.fold_hom (op := Atom.or) (op' := Atom.and) (b := 𝐟) (f := f) (m := Atom.neg) (s := P) ?_
  simp at this; exact this; apply neg_or

theorem join_neg : ⋁ P (¬ f) = ¬ ⋀ P f := by
  have := Finset.fold_hom (op := Atom.and) (op' := Atom.or) (b := 𝐭) (f := f) (m := Atom.neg) (s := P) ?_
  simp at this; exact this; apply neg_and

theorem le_implies_valid (p : a ≤ b) : ⊨ a → ⊨ b := by
  intro x; cases a <;> cases b <;> cases x <;> simp at *

@[simp] theorem TF_true_eval : TF 𝐭 = 𝐭 := by rfl
@[simp] theorem TF_false_eval : TF 𝐟 = 𝐭 := by rfl
@[simp] theorem TF_byzantine_eval : TF 𝐛 = 𝐟 := by rfl

@[simp] theorem T_true_eval : T 𝐭 = 𝐭 := by rfl
@[simp] theorem T_false_eval : T 𝐟 = 𝐟 := by rfl
@[simp] theorem T_byzantine_eval : T 𝐛 = 𝐟 := by rfl

@[simp] theorem B_true_eval : B 𝐭 = 𝐟 := by rfl
@[simp] theorem B_false_eval : B 𝐟 = 𝐟 := by rfl
@[simp] theorem B_byzantine_eval : B 𝐛 = 𝐭 := by rfl

@[simp] theorem neg_true_eval : (¬ 𝐭) = 𝐟 := by rfl
@[simp] theorem neg_false_eval : (¬ 𝐟) = 𝐭 := by rfl
@[simp] theorem neg_byzantine_eval : (¬ 𝐛) = 𝐛 := by rfl

@[simp] theorem and_left_false : (𝐟 ∧ a) = 𝐟 := by rfl
@[simp] theorem and_right_false : (a ∧ 𝐟) = 𝐟 := by cases a <;> rfl
@[simp] theorem and_left_true : (𝐭 ∧ a) = a := by cases a <;> rfl
@[simp] theorem and_right_true : (a ∧ 𝐭) = a := by cases a <;> rfl

@[simp] theorem or_left_false : (𝐟 ∨ a) = a := by cases a <;> rfl
@[simp] theorem or_right_false : (a ∨ 𝐟) = a := by cases a <;> rfl
@[simp] theorem or_left_true : (𝐭 ∨ a) = 𝐭 := by rfl
@[simp] theorem or_right_true : (a ∨ 𝐭) = 𝐭 := by cases a <;> rfl

@[simp] theorem and_neg_neg : (¬ a ∧ ¬ b) = ¬ (a ∨ b) := by cases a <;> cases b <;> rfl

@[simp] theorem or_right_byzantine_eq_byzantine : (a ∨ 𝐛) = 𝐛 ↔ a ≤ 𝐛 := by cases a <;> simp
@[simp] theorem or_left_byzantine_eq_byzantine : (𝐛 ∨ a) = 𝐛 ↔ a ≤ 𝐛 := by cases a <;> simp
@[simp] theorem or_right_byzantine_eq_true : (a ∨ 𝐛) = 𝐭 ↔ a = 𝐭 := by cases a <;> simp
@[simp] theorem or_left_byzantine_eq_true : (𝐛 ∨ a) = 𝐭 ↔ a = 𝐭 := by cases a <;> simp

@[simp] theorem le_or_left : b ≤ (b ∨ a) := by cases a <;> cases b <;> simp
@[simp] theorem le_or_right : b ≤ (a ∨ b) := by cases a <;> cases b <;> simp
@[simp] theorem byzantine_eq_and_byzantine : (a ∧ 𝐛) = 𝐛 ↔ 𝐛 ≤ a := by cases a <;> simp
@[simp] theorem byzantine_eq_byzantine_and : (𝐛 ∧ a) = 𝐛 ↔ 𝐛 ≤ a := by cases a <;> simp

@[simp] theorem isNotByzantine_le_byzantine : isNotByzantine a ≤ 𝐛 ↔ a = 𝐛 := by cases a <;> decide
@[simp] theorem neg_le_byzantine : (¬ a) ≤ 𝐛 ↔ 𝐛 ≤ a := by cases a <;> decide

@[simp] theorem and_le_left : (a ∧ b) ≤ a := by cases a <;> cases b <;> decide
@[simp] theorem and_le_right : (b ∧ a) ≤ a := by cases a <;> cases b <;> decide

theorem byzantine_le_impl : 𝐛 ≤ (a → b) ↔ a ≤ 𝐛 ∨ 𝐛 ≤ b := by
  cases a <;> cases b <;> simp

theorem byzantine_le_cases : 𝐛 ≤ a ↔ a = 𝐛 ∨ a = 𝐭 := by
  cases a <;> simp

@[simp] theorem valid_TB : ⊨ (TB a) ↔ 𝐛 ≤ a := by
  constructor <;> intro h <;> cases a <;> cases h <;> first | contradiction | simp!

theorem valid_and_TF : ⊨ a → ⊨ (TF a) → a = 𝐭 := by cases a <;> simp

theorem valid_TF_iff_TF_true : ⊨ (TF a) ↔ TF a = 𝐭 := by cases a <;> simp

theorem valid_TF : ⊨ (TF a) ↔ a = 𝐭 ∨ a = 𝐟 := by
  constructor <;> intro h <;> cases a <;> cases h <;> first | contradiction | simp

@[simp] theorem valid_T : ⊨ (T a) ↔ a = 𝐭 := by
  constructor <;> intro h <;> cases a <;> cases h <;> simp

theorem T_neg : T (¬ a) = F a := by
  cases a <;> simp [Atom.isFalse]

theorem Function.T_neg : T ∘ (¬ f) = F ∘ f := by
  funext a; simp [Lemmas.T_neg, Function.neg]

@[simp] theorem neg_eq_true : (¬ a) = 𝐭 ↔ a = 𝐟 := by cases a <;> simp
@[simp] theorem neg_eq_false : (¬ a) = 𝐟 ↔ a = 𝐭 := by cases a <;> simp
@[simp] theorem neg_eq_byzantine : (¬ a) = 𝐛 ↔ a = 𝐛 := by cases a <;> simp

@[simp] theorem Function.neg_eq_true {x} : (¬ f) x = 𝐭 ↔ f x = 𝐟 := by
  simp [Function.neg]

@[simp] theorem byzantine_meet_left_eq_true : (𝐛 ∧ a) = 𝐭 ↔ False := by
  cases a <;> simp

@[simp] theorem or_eq_false : (a ∨ b) = 𝐟 ↔ (a = 𝐟 ∧ b = 𝐟) := by
  cases a <;> cases b <;> simp

@[simp] theorem byzantine_meet_right_eq_true : (a ∧ 𝐛) = 𝐭 ↔ False := by
  cases a <;> simp

@[simp] theorem byzantine_lt : 𝐛 < a ↔ a = 𝐭 := by
  cases a <;> simp

@[simp] theorem lt_byzantine : a < 𝐛 ↔ a = 𝐟 := by
  cases a <;> simp

theorem le_or_implies : 𝐛 ≤ (a ∨ b) ↔ (a = 𝐟 → 𝐛 ≤ b) := by
  cases a <;> cases b <;> simp

theorem notValid_by_contra : (¬ ⊨ a) → ⊭ a := by
  intro p; cases a; simp;
  exfalso; refine p ?_; simp
  exfalso; refine p ?_; simp

theorem valid_cases : ⊨ a ↔ a = 𝐭 ∨ a = 𝐛 := by cases a <;> simp

@[simp] theorem byzantine_le_B : 𝐛 ≤ B a ↔ a = 𝐛 := by cases a <;> simp

theorem byzantine_le_TF : 𝐛 ≤ TF a ↔ a ≠ 𝐛 := by cases a <;> decide

@[simp] theorem byzantine_le_T : 𝐛 ≤ T a ↔ a = 𝐭 := by cases a <;> simp

theorem byzantine_le_TF_and : 𝐛 ≤ TF (a ∧ b)
  ↔ ((𝐛 ≤ a ∧ 𝐛 ≤ b) → a = 𝐭 ∧ b = 𝐭) := by
  cases a <;> cases b <;> simp

@[simp] theorem TF_and_B_false : (TF a ∧ B a) = 𝐟 := by
  cases a <;> simp [Three.Atom.and]

@[simp] theorem T_TF : (T (TF a)) = TF a := by
  cases a <;> simp

@[simp] theorem TF_TF : TF (TF a) = 𝐭 := by
  cases a <;> simp

@[simp] theorem TF_eq_false : (TF a) = 𝐟 ↔ a = 𝐛 := by
  cases a <;> simp

@[simp] theorem neg_TF : ¬ (TF a) = B a := by
  cases a <;> simp

theorem mp_weak : ((a → b) = 𝐭) → 𝐛 ≤ a → b = 𝐭 := by
  cases a <;> cases b <;> simp [Atom.impl, Atom.neg, Atom.or]

theorem mp_strong_true : ((a ⇀ b) = 𝐭) → a = 𝐭 → b = 𝐭 := by
  cases a <;> cases b <;> simp [Atom.strongImpl]

theorem mp_strong : (𝐛 ≤ (a ⇀ b)) → a = 𝐭 → b = 𝐭 := by
  cases a <;> cases b <;> simp [Atom.strongImpl]

end Lemmas

end Three

section Definition_2_3_1

/-- A finite semitopology over a type `P` of participants.

The `Fintype P` assumption ensures `P` is finite, which is needed so that folds over the full set
of participants (e.g. `□` and `◇`) are computable via `Finset.univ`. In practice, `P` represents
the set of participants in a distributed algorithm, which is always finite. Note that the paper does
not impose this assumption - it is an artifact of constructivity of the Lean formalisation. -/
structure FinSemitopology (P : Type) [Nonempty P] [DecidableEq P] [Fintype P] where
  Open : Finset (Finset P)
  empty_open : ∅ ∈ Open
  univ_open : Fintype.elems ∈ Open
  isOpen_sUnion : ∀ s : Finset (Finset P), (∀ t ∈ s, t ∈ Open) → s.biUnion id ∈ Open

end Definition_2_3_1

namespace FinSemitopology

open scoped Three.Function
open Three.Atom

section Definition_2_3_2

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

-- You will see ⊡(S) (see `quorum` below) and ⟐(S)
-- (see `contraquorum`) below. The S needs to be an explicit argument
-- of quorum/contraquorum because S is mentioned in the definition of ⊡ and ⟐
-- (via S.Open1), but S is not mentioned in the type (P → 𝟯 → 𝟯), so Lean's
-- unification cannot infer it.
abbrev quorum (S : FinSemitopology P) (f : P → 𝟯) := ⋁ S.Open1 (fun o => ⋀ o f)
scoped notation "⊡" => quorum
scoped notation "⊡" "(" S ")" => quorum S

abbrev contraquorum (S : FinSemitopology P) (f : P → 𝟯) := ⋀ S.Open1 (fun o => ⋁ o f)
scoped notation "⟐" => contraquorum
scoped notation "⟐" "(" S ")" => contraquorum S

end Definition_2_3_2

section

variable
  {P : Type}
  [Fintype P]
  {Q : Finset P}
  {f f' : P → 𝟯}
  (a b : 𝟯)

open Three.Lemmas

theorem everywhere_true : □ f = 𝐭 ↔ ∀ x, f x = 𝐭 := by simp [everywhere, meet_true]

theorem everywhere_byzantine : □ f = 𝐛 ↔ (∀ (x : P), 𝐛 ≤ f x) ∧ ∃ x, f x = 𝐛 := by
  simp [everywhere]

theorem somewhere_true : ◇ f = 𝐭 ↔ ∃ x, f x = 𝐭 := by simp [somewhere, join_true]

variable
  [DecidableEq P]
  [Nonempty P]
  {S : FinSemitopology P}

theorem quorum_true : ⊡(S) f = 𝐭 ↔ ∃ s ∈ S.Open1, ∀ x ∈ s, f x = 𝐭 := by
  simp [quorum]

theorem quorum_valid : 𝐛 ≤ ⊡(S) f ↔
                       (∃ s ∈ S.Open1, ∀ x ∈ s, 𝐛 ≤ f x) := by
  simp [quorum, le_join, byzantine_le_meet]

theorem contraquorum_true : ⟐(S) f = 𝐭 ↔ ∀ s ∈ S.Open1, ∃ x ∈ s, f x = 𝐭 := by
  simp [contraquorum]

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
  funext x; unfold Three.Function.neg Three.Function.and Three.Function.or; simp

theorem p1_3 [Fintype P] : (¬ (◇ (¬ f))) = □ f := by
  simp [somewhere, everywhere, join_neg];

theorem p1_4 [Fintype P] : (¬ (□ (¬ f))) = ◇ f := by
  simp [somewhere, everywhere, meet_neg];

theorem p1_5 [Nonempty P] [Fintype P] [DecidableEq P] {S : FinSemitopology P}
  : (¬ (⟐(S) (¬ f))) = ⊡(S) f := by
  simp [contraquorum, join_neg, Three.Function.neg_fold, meet_neg]

theorem p1_6 [Nonempty P] [Fintype P] [DecidableEq P] {S : FinSemitopology P}
  : (¬ (⊡(S) (¬ f))) = ⟐(S) f := by
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
  map_true : M 𝐭 = 𝐭 := by rfl
  map_false : M 𝐟 = 𝐟 := by rfl

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
  simpa [PreservesTruth.map_true] using Finset.fold_hom (b := 𝐭) (m := M) map_min

theorem map_join [MapMax M]
  : ⋁ Q (M ∘ f) = M (⋁ Q f) := by
  simpa [PreservesTruth.map_false] using Finset.fold_hom (b := 𝐟) (m := M) map_max

theorem map_everywhere [Fintype P] [MapMin M]
  : □ (M ∘ f) = M (□ f) := by
  simpa [PreservesTruth.map_true] using Finset.fold_hom (b := 𝐭) (m := M) map_min

theorem map_somewhere [Fintype P] [MapMax M] : ◇ (M ∘ f) = M (◇ f) := by
  simpa [PreservesTruth.map_false] using Finset.fold_hom (b := 𝐟) (m := M) map_max

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

section Definition_2_4_1

class Twined3 {P : Type} [Nonempty P] [DecidableEq P] [Fintype P] [DecidableEq P] (S : FinSemitopology P) where
  twined : ∀ {a b c}, a ∈ S.Open1 → b ∈ S.Open1 → c ∈ S.Open1 → a ∩ b ∩ c ∈ S.Open1

export Twined3 (twined)

end Definition_2_4_1

namespace Example_2_4_3
-- Not formalised
end Example_2_4_3

namespace Theorem_2_4_5

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

theorem t2' : 𝐛 ≤ (⊡(S) f ∧ ⊡(S) f') → (⊨ (⟐(S) (f ∧ f'))) := by
  apply le_implies_valid t

end Theorem_2_4_5

namespace Corollary_2_4_6

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
  have x := Proposition_2_2_3.p9.mp (Theorem_2_4_5.t (f := ¬ f) (f' := ¬ f') (S := S))
  simpa [← Lemma_2_3_3.p1_2, Lemma_2_3_3.p1_5, Three.Lemmas.neg_and
        , Lemma_2_3_3.p1_6, Lemma_2_3_3.p1_6] using x

theorem t2 : ⊨ (⊡(S) (f ∨ f')) → ⊨ (⟐(S) f ∨ ⟐(S) f') := Three.Lemmas.le_implies_valid t1

end Corollary_2_4_6

namespace Remark_2_4_7

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
  : ⊨ (⊡(S) f) -> ⊡(S) f = 𝐭 := by
  intro h; simp [quorum, le_join] at h; obtain ⟨h1, h2, h3⟩ := h
  have ⟨qs, qm, p⟩ := q' q; simp
  refine ⟨qs ∩ h1, ?_, ?_⟩;
  have t := twined.twined qm qm h2; simpa using t
  intro x xq; obtain ⟨x1, x2⟩ := by simpa [Finset.mem_inter] using xq
  cases valid_TF.mp (p x x1); assumption
  next h => have := h3 _ x2; rw [h] at this; contradiction

include q in
theorem t2 [twined : Twined3 S] : ⊨ (⊡(S) f) -> ⊨ (T (⟐(S) f)) := by
  have h := Theorem_2_4_5.t (f := T ∘ f) (f' := T ∘ f) (S := S)
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
  le_implies_valid Theorem_2_4_5.t

omit q in
theorem t5_2 [twined : Twined3 S] : ⊨ (⊡(S) (f ∨ f')) → ⊨ (⟐(S) f ∨ ⟐(S) f') := by
  intro p; exact Corollary_2_4_6.t2 p

end Remark_2_4_7

namespace Remark_2_4_8

open Three.Lemmas

variable
  {P : Type}
  [Nonempty P]
  [Fintype P]
  [DecidableEq P]
  {S : FinSemitopology P}

theorem t (h : ∀ (f f' : P → 𝟯), (⊡(S) f ∧ ⊡(S) f') ≤ ⟐(S) (f ∧ f'))
    {a b c : Finset P} (ha : a ∈ S.Open1) (hb : b ∈ S.Open1) (hc : c ∈ S.Open1)
    : (a ∩ b ∩ c).Nonempty := by
  specialize h (fun p => if p ∈ a then 𝐭 else 𝐛)
               (fun p => if p ∈ b then 𝐭 else 𝐛)
  have hqa : ⊡(S) (fun p => if p ∈ a then 𝐭 else 𝐛) = 𝐭 :=
    quorum_true.mpr ⟨a, ha, fun x hx => by simp [hx]⟩
  have hqb : ⊡(S) (fun p => if p ∈ b then 𝐭 else 𝐛) = 𝐭 :=
    quorum_true.mpr ⟨b, hb, fun x hx => by simp [hx]⟩
  rw [hqa, hqb] at h; simp at h
  obtain ⟨x, hxc, hx⟩ := h c hc
  have hxa : x ∈ a := by by_contra hna; simp [hna] at hx
  have hxb : x ∈ b := by by_contra hnb; simp [hnb] at hx
  exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hxa, hxb⟩, hxc⟩⟩

end Remark_2_4_8

section Definition_2_5_1

variable
  {P : Type}
  [Fintype P]
  [Nonempty P]
  [DecidableEq P]
  {S : FinSemitopology P}
  {vote observe : P → 𝟯}

class ThyVote (S : FinSemitopology P) (vote observe : P → 𝟯) where
  observe? p : (observe p → ⊡(S) vote) = 𝐭
  observe! p : (⊡(S) vote ⇀ observe p) = 𝐭
  correct : ⊡(S) (TF ∘ vote) = 𝐭
  observeN? p : (¬ (observe p) → ⊡(S) (¬ vote)) = 𝐭
  observeN! p : (⊡(S) (¬ vote) ⇀ (¬ (observe p))) = 𝐭
  twined3 f f' : (⊡(S) f ∧ ⊡(S) f') ≤ ⟐(S) (f ∧ f')

end Definition_2_5_1

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
  rw [Proposition_2_2_3.p4]; intro h; obtain ⟨x, t⟩ := somewhere_true.mp h
  simp [quorum, le_join, le_meet]
  obtain ⟨s, xo, sp⟩ := by simpa [quorum] using mp_weak (i.observe? x) (byzantine_le.mpr (.inr t))
  refine ⟨_, xo, ?_⟩; intro y ys; simp [sp _ ys]

theorem t2 : ⊨ (⊡(S) vote ⇀ □ observe) := by
  rw [Proposition_2_2_3.p5, everywhere]; intro h;
  simp; intro p; exact mp_strong_true (i.observe! p) h

theorem t3 : ⊨ (◇ (¬ observe) → ⊡(S) (¬ vote)) := by
  rw [Proposition_2_2_3.p4]; intro h; obtain ⟨x, t⟩ := somewhere_true.mp h
  simp [quorum, le_join, le_meet]
  obtain ⟨s, xo, sp⟩ := by simpa [quorum] using mp_weak (i.observeN? x) (byzantine_le.mpr (.inr t))
  refine ⟨_, xo, ?_⟩; intro y ys; simp [sp _ ys]

theorem t4 : ⊨ (⊡(S) vote ⇀ □ observe) := by
  rw [Proposition_2_2_3.p5, everywhere]; intro h;
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
theorem t : ⊭ (◇ (T ∘ observe) ∧ ◇ (T ∘ (¬ observe))) := by
  apply notValid_by_contra
  intro h; rw [Valid, le_and] at h; have ⟨h1, h2⟩ := h
  simp [Remark_2_3_5.map_somewhere] at h1 h2
  have ⟨p, px⟩ := h1; have ⟨p', px'⟩ := h2
  have votep := mp_weak (i.observe? p) (byzantine_le.mpr (.inr px))
  have votep' := mp_weak (i.observeN? p') (by simp [px'])
  have q : (⊡(S) vote ∧ ⊡(S) (¬ vote)) = 𝐭 :=
    Three.Lemmas.and_true.mpr ⟨votep, votep'⟩
  have v : (⟐(S) (vote ∧ (¬ vote))) = 𝐭 := by
    have x := i.twined3 vote (¬ vote); simpa [q] using x
  rw [contraquorum, meet_true] at v
  have k : ⊨ (⟐(S) (B ∘ vote)) := by
    simp [contraquorum, le_meet]; intro s sm
    have ⟨y, ym, yp⟩ := join_true.mp (v _ sm)
    refine ⟨_, ym, ?_⟩
    simp [Three.Function.and] at yp
    apply Proposition_2_2_3.p7 (a := vote y) |>.mp
    simp [yp]
  have c : ⊡(S) (TF ∘ vote) = 𝐭 := i.correct
  have kc : ⊨ (⊡(S) (TF ∘ vote) ∧ (⟐(S) (B ∘ vote))) := by
    rw [Valid, le_and]; constructor; simp [c]; exact k
  have r := Lemma_2_3_7.c1 kc
  simp [somewhere, le_join] at r

end Proposition_2_5_7
