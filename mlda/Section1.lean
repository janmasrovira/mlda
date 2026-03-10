import mlda.Base

inductive Three : Type where
  | false
  | byzantine
  | true

notation "𝟯" => Three

namespace Three

namespace Atom

variable
  {X : Type}

def neg : 𝟯 → 𝟯
  | false => true
  | byzantine => byzantine
  | true => false
scoped prefix:75 "¬ " => neg

def and : 𝟯 → 𝟯 → 𝟯
  | true, true => true
  | byzantine, true => byzantine
  | true, byzantine => byzantine
  | byzantine, byzantine => byzantine
  | _, _ => false

scoped infixl:35 " ∧ " => and

instance : Std.Associative and where
  assoc := by intro a b c; cases a <;> cases b <;> cases c <;> simp!

instance : Std.Commutative and where
  comm := by intro a b; cases a <;> cases b <;> simp!

instance : Std.LawfulCommIdentity and true where
  left_id := by intro a; cases a <;> simp!

def or : 𝟯 → 𝟯 → 𝟯
  | false, false => false
  | false, byzantine => byzantine
  | byzantine, false => byzantine
  | byzantine, byzantine => byzantine
  | _, _ => true

scoped infixl:30 " ∨ " => or

instance : Std.Associative or where
  assoc := by intro a b c; cases a <;> cases b <;> cases c <;> simp!

instance : Std.Commutative or where
  comm := by intro a b; cases a <;> cases b <;> simp!

instance : Std.LawfulCommIdentity or false where
  left_id := by intro a; cases a <;> simp!

def xor : 𝟯 → 𝟯 → 𝟯
  | byzantine, _ => byzantine
  | _, byzantine => byzantine
  | true, true => false
  | false, false => false
  | _, _ => true
scoped infixl:30 " ⊕ " => xor

@[simp] abbrev impl (a b : 𝟯) : 𝟯 := (¬ a) ∨ b
scoped infixl:25 " → " => impl

def isTrue : 𝟯 → 𝟯
 | true => true
 | _ => false
scoped notation "T" => isTrue

def isByzantine : 𝟯 → 𝟯
 | byzantine => true
 | _ => false
scoped notation "B" => isByzantine

def isFalse : 𝟯 → 𝟯
 | false => true
 | _ => false
scoped notation "F" => isFalse

def isNotFalse : 𝟯 → 𝟯
 | false => false
 | _ => true
scoped notation "TB" => isNotFalse

def isNotByzantine : 𝟯 → 𝟯
 | byzantine => false
 | _ => true
scoped notation "TF" => isNotByzantine

def strongImpl : 𝟯 → 𝟯 → 𝟯
 | false, _ => true
 | byzantine, true => true
 | byzantine, _ => byzantine
 | true, true => true
 | true, _ => false
scoped infixl:25 " ⇀ " => strongImpl

instance : Ord 𝟯 where
  compare := fun
   | false, false => .eq
   | false, _ => .lt
   | _, false => .gt
   | byzantine, byzantine => .eq
   | byzantine, true => .lt
   | true, byzantine => .gt
   | true, true => .eq

instance : Max Three where
  max := or

instance : Min Three where
  min := and

instance : LinearOrder Three := by
  let toFin : 𝟯 → Fin 3
    | false => 0
    | byzantine => 1
    | true => 2
  apply LinearOrder.liftWithOrd toFin
  intro x y p; cases x <;> cases y <;> cases p <;> rfl
  repeat (intro x y; cases x <;> cases y <;> rfl)

instance : BoundedOrder Three where
  bot := false
  bot_le := by intro a; cases a <;> decide
  top := true
  le_top := by intro a; cases a <;> decide

instance : DistribLattice Three where
  le_sup_inf := by intro a b c; cases a <;> cases b <;> cases c <;> decide

abbrev Valid (p : 𝟯) : Prop := byzantine ≤ p
scoped notation "⊨" => Valid

abbrev NotValid (p : 𝟯) : Prop := p = .false
scoped notation "⊭" => NotValid

-- TODO make sure all numbers align with the pdf
namespace Proposition_2_2_2

variable {a b : 𝟯}

@[simp] theorem p1_1 : ⊨ true := by decide
@[simp] theorem p1_2 : ⊨ byzantine := by decide
@[simp] theorem p1_3 : ⊭ false := by rfl
@[simp] theorem p1_4 : ¬ (⊨ false) := by intro k; cases k
@[simp] theorem p1_5 : ¬ (⊭ true) := by intro k; cases k
@[simp] theorem p1_6 : ¬ (⊭ byzantine) := by intro k; cases k

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

theorem p4 : ⊨ (a → b) ↔ ((a = true) → ⊨ (TB b)) := by
  cases a <;> cases b <;> simp [impl, or, neg, isNotFalse]

theorem p5 : ⊨ (a ⇀ b) ↔ ((a = true) → (b = true)) := by
  cases a <;> cases b <;> simp [strongImpl]

theorem p6 : ⊨ (a ∨ ¬ a) := by cases a <;> simp!

theorem p7 : ⊨ (a ∧ ¬ a) ↔ a = byzantine := by
  constructor <;> cases a <;> simp!

theorem p8 : ⊨ a ↔ (TF a = T a) := by cases a <;> simp!

theorem p9 : a ≤ b ↔ ((¬ b) ≤ ¬ a) := by
  constructor <;> cases a <;> cases b <;> decide

end Proposition_2_2_2

end Atom

namespace Function

open scoped Three.Atom

variable {X : Type}

abbrev bigAnd (P : Finset X) (f : X → 𝟯) : 𝟯 := P.fold min true f
scoped notation "⋀" => bigAnd

abbrev bigOr (P : Finset X) (f : X → 𝟯) : 𝟯 := P.fold max false f
scoped notation "⋁" => bigOr

@[simp] def lift1 (op : 𝟯 → 𝟯) (f : X → 𝟯) : X → 𝟯 := op ∘ f
@[simp] def lift2 (op : 𝟯 → 𝟯 → 𝟯) (f f' : X → 𝟯) : X → 𝟯 := fun x => op (f x) (f' x)

abbrev neg (f : X → 𝟯) : X → 𝟯 := Atom.neg ∘ f
scoped prefix:75 "¬ᶠ" => neg -- TODO add supescript l to all lifted operators

theorem neg_fold {f : X → 𝟯} : (fun x => ¬ (f x)) = (¬ᶠ f) := by rfl

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

@[simp] theorem T_true : T a = true ↔ a = true := by cases a <;> decide

theorem false_or_byzantine_le : (a = Three.false) ∨ .byzantine ≤ a := by cases a <;> decide

theorem true_or_le_byzantine : (a = Three.true) ∨ a ≤ .byzantine := by cases a <;> decide

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

@[simp] theorem Function.neg_applied {x} : (¬ᶠ f) x = ¬ (f x) := by simp [Function.neg]

theorem Function.neg_and : (¬ᶠ (f ∧ f')) = (¬ᶠ f ∨ ¬ᶠ f') := by
  rw [Three.Function.and, Three.Function.or, Three.Function.neg]
  funext; apply Lemmas.neg_and

@[simp] theorem neg_neg : (¬ ¬ a) = a := by
  cases a <;> rfl

@[simp] theorem Function.neg_neg : (¬ᶠ (¬ᶠ f)) = f := by
  unfold Three.Function.neg; funext a; rw [Function.comp, Function.comp]
  cases h : f a <;> rfl

@[simp] theorem byzantine_le_neg : byzantine ≤ ¬ a ↔ a ≤ byzantine := by
  cases a <;> decide

theorem le_or : c ≤ (a ∨ b) ↔ (c ≤ a ∨ c ≤ b) := by
  cases a <;> cases b <;> cases c <;> decide

theorem or_le : (a ∨ b) ≤ c ↔ (a ≤ c ∧ b ≤ c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem le_and : c ≤ (a ∧ b) ↔ (c ≤ a ∧ c ≤ b) := by
  cases a <;> cases b <;> cases c <;> decide

theorem and_le : (a ∧ b) ≤ c ↔ (a ≤ c ∨ b ≤ c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem and_true : (a ∧ b) = Three.true ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> decide

theorem and_byzantine : (a ∧ b) = Three.byzantine ↔ (a = byzantine ∧ byzantine ≤ b) ∨ (b = byzantine ∧ byzantine ≤ a) := by
  cases a <;> cases b <;> decide

theorem byzantine_le_and : .byzantine ≤ (a ∧ b) ↔ (byzantine ≤ a ∧ byzantine ≤ b) := by
  cases a <;> cases b <;> decide

theorem and_false : (a ∧ b) = .false ↔ (a = false ∨ b = false) := by
  cases a <;> cases b <;> decide

theorem or_true : (a ∨ b) = .true ↔ (a = true ∨ b = true) := by
  cases a <;> cases b <;> decide

theorem impl_true : (a → b) = .true ↔ (byzantine ≤ a → b = true) := by
  cases a <;> cases b <;> decide

theorem impl_byzantine : (a → b) = .byzantine ↔
    (a ≤ byzantine ∨ b ≠ byzantine) → (a = byzantine ∧ b ≤ byzantine) := by
  cases a <;> cases b <;> decide

@[simp] theorem bot_le : false ≤ a ↔ True := by
  cases a <;> decide

@[simp] theorem le_bot : a ≤ false ↔ a = false := by
  cases a <;> decide

@[simp] theorem false_lt : false < a ↔ byzantine ≤ a := by
  cases a <;> decide

@[simp] theorem lt_true : a < true ↔ a ≤ byzantine := by
  cases a <;> decide

@[simp] theorem top_le : true ≤ a ↔ a = true := by
  cases a <;> decide

@[simp] theorem le_top : a ≤ true ↔ True := by
  cases a <;> decide

theorem byzantine_le : byzantine ≤ a ↔ a = byzantine ∨ a = true := by
  cases a <;> decide

theorem le_byzantine : a ≤ byzantine ↔ a = false ∨ a = byzantine := by
  cases a <;> decide

theorem le_helper (p : byzantine ≤ a → b ≤ byzantine → a ≤ b) : a ≤ b := by
  cases a <;> cases b <;> try decide
  repeat (simp at p)

theorem le_by_cases (c1 : a = true → b ≤ byzantine → b = true)
                    (c2 : a = byzantine → b ≤ byzantine → byzantine ≤ b)
 : a ≤ b := by
  cases a <;> cases b <;> try decide
  repeat (simp at c1 c2)

@[simp] theorem meet_false : ⋀ P f = false ↔ ∃ x ∈ P, f x = false := by
  unfold bigAnd;
  have h : P.fold min true f ≤ false ↔ _ ∨ ∃ x ∈ P, f x ≤ false :=
    Finset.fold_min_le false
  simpa using h

@[simp] theorem meet_byzantine : P.fold min true f = byzantine ↔ (∀ x ∈ P, byzantine ≤ f x) ∧ ∃ x ∈ P, f x = byzantine := by
  have h1 : P.fold min true f ≤ byzantine ↔ _ ∨ ∃ x ∈ P, f x ≤ byzantine :=
    Finset.fold_min_le byzantine
  have h2 : byzantine ≤ P.fold min true f ↔ _ ∧ ∀ x ∈ P, byzantine ≤ f x :=
    Finset.le_fold_min byzantine
  generalize P.fold Atom.and true f = y at *
  constructor
  intro x; rw [x] at h1 h2; simp at h1 h2;
  constructor; assumption; rcases h1 with ⟨p1, p2, p3⟩; exists p1; constructor; assumption
  apply le_antisymm; assumption; apply h2; assumption
  rintro ⟨a, b⟩; apply le_antisymm; apply h1.mpr; simp; rcases b with ⟨p1, p2, p3⟩;
  exists p1; constructor; assumption; exact ge_of_eq p3.symm
  apply h2.mpr; simp; assumption

@[simp] theorem meet_true : P.fold min true f = true ↔ ∀ x ∈ P, f x = true := by
  have h : true ≤ P.fold min true f ↔ _ ∧ ∀ x ∈ P, true ≤ f x :=
    Finset.le_fold_min true
  simpa using h

@[simp] theorem join_false : ⋁ P f = false ↔ ∀ x ∈ P, f x = false := by
  unfold bigOr;
  have h : P.fold max false f ≤ false ↔ _ ∧ ∀ x ∈ P, f x ≤ false :=
    Finset.fold_max_le false
  simpa using h

@[simp] theorem join_le_byzantine : P.fold max false f ≤ byzantine ↔ (∀ x ∈ P, f x ≤ byzantine) := by
  have h1 : P.fold max false f ≤ byzantine ↔ _ ∧ ∀ x ∈ P, f x ≤ byzantine :=
    Finset.fold_max_le byzantine
  simpa using h1

@[simp] theorem byzantine_le_meet : byzantine ≤ P.fold min true f ↔ ∀ x ∈ P, f x ≥ byzantine := by
  have h2 : byzantine ≤ P.fold min true f ↔ _ ∧ ∀ x ∈ P, byzantine ≤ f x :=
    Finset.le_fold_min (f := f) byzantine
  simpa using h2

@[simp] theorem byzantine_le_join : byzantine ≤ P.fold max false f ↔ ∃ x ∈ P, f x ≥ byzantine := by
  have h2 : byzantine ≤ P.fold max false f ↔ _ ∨ ∃ x ∈ P, f x ≥ byzantine :=
    Finset.le_fold_max byzantine
  simpa using h2

theorem le_meet : a ≤ ⋀ P f ↔ ∀ x ∈ P, a ≤ f x := by
  simpa using (Finset.le_fold_min (b := true) a)

theorem meet_le : ⋀ P f ≤ a ↔ a = true ∨ ∃ x ∈ P, f x ≤ a := by
  simpa using (Finset.fold_min_le (b := true) a)

@[simp] theorem meet_le_byzantine : P.fold min true f ≤ byzantine ↔ (∃ x ∈ P, f x ≤ byzantine) := by
  simp [meet_le]


theorem le_join : a ≤ P.fold max false f ↔ a = false ∨ ∃ x ∈ P, f x ≥ a := by
  simpa using (Finset.le_fold_max (b := false) a)

theorem join_le : ⋁ P f ≤ a ↔ ∀ x ∈ P, f x ≤ a := by
  simpa using (Finset.fold_max_le (b := false) a)

theorem join_byzantine : P.fold max false f = byzantine ↔ (∀ x ∈ P, f x ≤ byzantine) ∧ ∃ x ∈ P, f x = byzantine := by
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

@[simp] theorem join_true : ⋁ P f = true ↔ ∃ x ∈ P, f x = true := by
  unfold bigOr;
  have h : true ≤ P.fold max false f ↔ _ ∨ ∃ x ∈ P, true ≤ f x :=
    Finset.le_fold_max true
  simpa using h

theorem meet_neg : ⋀ P (Atom.neg ∘ f) = ¬ ⋁ P f := by
  have := Finset.fold_hom (op := Atom.or) (op' := Atom.and) (b := false) (f := f) (m := Atom.neg) (s := P) ?_
  simp at this; exact this; apply neg_or

theorem join_neg : ⋁ P (¬ᶠ f) = ¬ ⋀ P f := by
  have := Finset.fold_hom (op := Atom.and) (op' := Atom.or) (b := true) (f := f) (m := Atom.neg) (s := P) ?_
  simp at this; exact this; apply neg_and

theorem le_implies_valid (p : a ≤ b) : ⊨ a → ⊨ b := by
  intro x; cases a <;> cases b <;> cases x <;> simp at *

@[simp] theorem TF_true_eval : TF true = true := by rfl
@[simp] theorem TF_false_eval : TF false = true := by rfl
@[simp] theorem TF_byzantine_eval : TF byzantine = false := by rfl

@[simp] theorem T_true_eval : T true = true := by rfl
@[simp] theorem T_false_eval : T false = false := by rfl
@[simp] theorem T_byzantine_eval : T byzantine = false := by rfl

@[simp] theorem B_true_eval : B true = false := by rfl
@[simp] theorem B_false_eval : B false = false := by rfl
@[simp] theorem B_byzantine_eval : B byzantine = true := by rfl

@[simp] theorem neg_true_eval : (¬ true) = false := by rfl
@[simp] theorem neg_false_eval : (¬ false) = true := by rfl
@[simp] theorem neg_byzantine_eval : (¬ byzantine) = byzantine := by rfl

@[simp] theorem and_left_false : (false ∧ a) = false := by rfl
@[simp] theorem and_right_false : (a ∧ false) = false := by cases a <;> rfl
@[simp] theorem and_left_true : (true ∧ a) = a := by cases a <;> rfl
@[simp] theorem and_right_true : (a ∧ true) = a := by cases a <;> rfl

@[simp] theorem or_left_false : (false ∨ a) = a := by cases a <;> rfl
@[simp] theorem or_right_false : (a ∨ false) = a := by cases a <;> rfl
@[simp] theorem or_left_true : (true ∨ a) = true := by rfl
@[simp] theorem or_right_true : (a ∨ true) = true := by cases a <;> rfl

@[simp] theorem and_neg_neg : (¬ a ∧ ¬ b) = ¬ (a ∨ b) := by cases a <;> cases b <;> rfl

@[simp] theorem or_right_byzantine_eq_byzantine : (a ∨ byzantine) = byzantine ↔ a ≤ byzantine := by cases a <;> simp
@[simp] theorem or_left_byzantine_eq_byzantine : (byzantine ∨ a) = byzantine ↔ a ≤ byzantine := by cases a <;> simp
@[simp] theorem or_right_byzantine_eq_true : (a ∨ byzantine) = true ↔ a = true := by cases a <;> simp
@[simp] theorem or_left_byzantine_eq_true : (byzantine ∨ a) = true ↔ a = true := by cases a <;> simp

@[simp] theorem le_or_left : b ≤ (b ∨ a) := by cases a <;> cases b <;> simp
@[simp] theorem le_or_right : b ≤ (a ∨ b) := by cases a <;> cases b <;> simp
@[simp] theorem byzantine_eq_and_byzantine : (a ∧ byzantine) = byzantine ↔ byzantine ≤ a := by cases a <;> simp
@[simp] theorem byzantine_eq_byzantine_and : (byzantine ∧ a) = byzantine ↔ byzantine ≤ a := by cases a <;> simp

@[simp] theorem isNotByzantine_le_byzantine : isNotByzantine a ≤ Three.byzantine ↔ a = byzantine := by cases a <;> decide
@[simp] theorem neg_le_byzantine : (¬ a) ≤ byzantine ↔ byzantine ≤ a := by cases a <;> decide

@[simp] theorem and_le_left : (a ∧ b) ≤ a := by cases a <;> cases b <;> decide
@[simp] theorem and_le_right : (b ∧ a) ≤ a := by cases a <;> cases b <;> decide

theorem byzantine_le_impl : byzantine ≤ (a → b) ↔ a ≤ byzantine ∨ byzantine ≤ b := by
  cases a <;> cases b <;> simp

theorem byzantine_le_cases : byzantine ≤ a ↔ a = byzantine ∨ a = true := by
  cases a <;> simp

@[simp] theorem valid_TB : ⊨ (TB a) ↔ byzantine ≤ a := by
  constructor <;> intro h <;> cases a <;> cases h <;> first | contradiction | simp!

theorem valid_and_TF : ⊨ a → ⊨ (TF a) → a = true := by cases a <;> simp

theorem valid_TF_iff_TF_true : ⊨ (TF a) ↔ TF a = true := by cases a <;> simp

theorem valid_TF : ⊨ (TF a) ↔ a = true ∨ a = false := by
  constructor <;> intro h <;> cases a <;> cases h <;> first | contradiction | simp

@[simp] theorem valid_T : ⊨ (T a) ↔ a = true := by
  constructor <;> intro h <;> cases a <;> cases h <;> simp

theorem T_neg : T (¬ a) = F a := by
  cases a <;> simp [Atom.isFalse]

theorem Function.T_neg : T ∘ (¬ᶠ f) = F ∘ f := by
  funext a; simp [Lemmas.T_neg, Function.neg]

@[simp] theorem neg_eq_true : (¬ a) = true ↔ a = false := by cases a <;> simp
@[simp] theorem neg_eq_false : (¬ a) = false ↔ a = true := by cases a <;> simp
@[simp] theorem neg_eq_byzantine : (¬ a) = byzantine ↔ a = byzantine := by cases a <;> simp

@[simp] theorem Function.neg_eq_true {x} : (¬ᶠ f) x = true ↔ f x = false := by
  simp [Function.neg]

@[simp] theorem byzantine_meet_left_eq_true : (byzantine ∧ a) = true ↔ False := by
  cases a <;> simp

@[simp] theorem or_eq_false : (a ∨ b) = false ↔ (a = false ∧ b = false) := by
  cases a <;> cases b <;> simp

@[simp] theorem byzantine_meet_right_eq_true : (a ∧ byzantine) = true ↔ False := by
  cases a <;> simp

@[simp] theorem byzantine_lt : byzantine < a ↔ a = true := by
  cases a <;> simp

@[simp] theorem lt_byzantine : a < byzantine ↔ a = false := by
  cases a <;> simp

theorem le_or_implies : byzantine ≤ (a ∨ b) ↔ (a = false → byzantine ≤ b) := by
  cases a <;> cases b <;> simp

theorem notValid_by_contra : (¬ ⊨ a) → ⊭ a := by
  intro p; cases a; simp;
  exfalso; refine p ?_; simp
  exfalso; refine p ?_; simp

theorem valid_cases : ⊨ a ↔ a = true ∨ a = byzantine := by cases a <;> simp

@[simp] theorem byzantine_le_B : byzantine ≤ B a ↔ a = byzantine := by cases a <;> simp

theorem byzantine_le_TF : byzantine ≤ TF a ↔ a ≠ byzantine := by cases a <;> decide

@[simp] theorem byzantine_le_T : byzantine ≤ T a ↔ a = true := by cases a <;> simp

theorem byzantine_le_TF_and : byzantine ≤ TF (a ∧ b)
  ↔ ((byzantine ≤ a ∧ byzantine ≤ b) → a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

@[simp] theorem TF_and_B_false : (TF a ∧ B a) = false := by
  cases a <;> simp [Three.Atom.and]

@[simp] theorem T_TF : (T (TF a)) = TF a := by
  cases a <;> simp

@[simp] theorem TF_TF : TF (TF a) = true := by
  cases a <;> simp

@[simp] theorem TF_eq_false : (TF a) = false ↔ a = byzantine := by
  cases a <;> simp

@[simp] theorem neg_TF : ¬ (TF a) = B a := by
  cases a <;> simp

theorem mp_weak : ((a → b) = true) → byzantine ≤ a → b = true := by
  cases a <;> cases b <;> simp [Atom.impl, Atom.neg, Atom.or]

theorem mp_strong_true : ((a ⇀ b) = true) → a = true → b = true := by
  cases a <;> cases b <;> simp [Atom.strongImpl]

theorem mp_strong : (byzantine ≤ (a ⇀ b)) → a = true → b = true := by
  cases a <;> cases b <;> simp [Atom.strongImpl]

end Lemmas

end Three
