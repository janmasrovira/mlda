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
-- TODO document Fintype P
structure FinSemitopology (P : Type) [Nonempty P] [DecidableEq P] [Fintype P] where
  Open : Finset (Finset P)
  empty_open : ∅ ∈ Open
  univ_open : Fintype.elems ∈ Open
  isOpen_sUnion : ∀ s : Finset (Finset P), (∀ t ∈ s, t ∈ Open) → s.biUnion id ∈ Open

namespace FinSemitopology

open scoped Three.Function
open Three.Atom

section

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
-- TODO try to fix S

def Open1 : Finset (Finset P) := S.Open.filter (·.Nonempty)

def univ_in_Open1 : Finset.univ ∈ S.Open1 := by
  simp [Open1]; exact S.univ_open

abbrev everywhere := ⋀ ℙ f
scoped notation "□" => everywhere

abbrev somewhere := ⋁ ℙ f
scoped notation "◇" => somewhere

abbrev quorum := ⋁ S.Open1 (fun o => ⋀ o f)
scoped notation "⊡" => quorum
scoped notation "⊡" "(" A ")" => quorum (S := A)

abbrev contraquorum := ⋀ S.Open1 (fun o => ⋁ o f)
scoped notation "⟐" => contraquorum
scoped notation "⟐" "(" A ")" => contraquorum (S := A)

end

section

variable
  {P : Type}
  [Fintype P]
  {Q : Finset P}
  {f f' : P → 𝟯}
  (a b : 𝟯)

open Three.Lemmas

theorem everywhere_true : □ f = .true ↔ ∀ x, f x = .true := by simp [everywhere, meet_true]

theorem everywhere_byzantine : □ f = .byzantine ↔ (∀ (x : P), Three.byzantine ≤ f x) ∧ ∃ x, f x = Three.byzantine := by
  simp [everywhere]

theorem somewhere_true : ◇ f = .true ↔ ∃ x, f x = .true := by simp [somewhere, join_true]

variable
  [DecidableEq P]
  [Nonempty P]
  {S : FinSemitopology P}

theorem quorum_true : ⊡(S) f = .true ↔ ∃ s ∈ S.Open1, ∀ x ∈ s, f x = .true := by
  simp [quorum]

theorem quorum_valid : .byzantine ≤ ⊡(S) f ↔
                       (∃ s ∈ S.Open1, ∀ x ∈ s, Three.byzantine ≤ f x) := by
  simp [quorum, le_join, byzantine_le_meet]

theorem contraquorum_true : ⟐(S) f = .true ↔ ∀ s ∈ S.Open1, ∃ x ∈ s, f x = .true := by
  simp [contraquorum]

end

namespace Lemma_2_3_3

variable
  {P : Type}
  {f f' : P → 𝟯}
  {a : 𝟯}

open Three.Lemmas

theorem p1_1 : (¬ᶠ (f ∧ f')) = (¬ᶠ f ∨ ¬ᶠ f') := by
  funext x; unfold Three.Function.neg Three.Function.and Three.Function.or; simp; cases f x <;> cases f' x <;> simp!

theorem p1_2 : (¬ᶠ (f ∨ f')) = (¬ᶠ f ∧ ¬ᶠ f') := by
  funext x; unfold Three.Function.neg Three.Function.and Three.Function.or; simp

theorem p1_3 [Fintype P] : (¬ (◇ (¬ᶠ f))) = □ f := by
  simp [somewhere, everywhere, join_neg];

theorem p1_4 [Fintype P] : (¬ (□ (¬ᶠ f))) = ◇ f := by
  simp [somewhere, everywhere, meet_neg];

theorem p1_5 [Nonempty P] [Fintype P] [DecidableEq P] {S : FinSemitopology P}
  : (¬ (⟐(S) (¬ᶠ f))) = ⊡(S) f := by
  simp [contraquorum, join_neg, Three.Function.neg_fold, meet_neg]

theorem p1_6 [Nonempty P] [Fintype P] [DecidableEq P] {S : FinSemitopology P}
  : (¬ (⊡(S) (¬ᶠ f))) = ⟐(S) f := by
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
  map_true : M true = Three.true := by rfl
  map_false : M false = Three.false := by rfl

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
  simpa [PreservesTruth.map_true] using Finset.fold_hom (b := Three.true) (m := M) map_min

theorem map_join [MapMax M]
  : ⋁ Q (M ∘ f) = M (⋁ Q f) := by
  simpa [PreservesTruth.map_false] using Finset.fold_hom (b := Three.false) (m := M) map_max

theorem map_everywhere [Fintype P] [MapMin M]
  : □ (M ∘ f) = M (□ f) := by
  simpa [PreservesTruth.map_true] using Finset.fold_hom (b := Three.true) (m := M) map_min

theorem map_somewhere [Fintype P] [MapMax M] : ◇ (M ∘ f) = M (◇ f) := by
  simpa [PreservesTruth.map_false] using Finset.fold_hom (b := Three.false) (m := M) map_max

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

class Twined3 {P : Type} [Nonempty P] [DecidableEq P] [Fintype P] [DecidableEq P] (S : FinSemitopology P) where
  twined : ∀ {a b c}, a ∈ S.Open1 → b ∈ S.Open1 → c ∈ S.Open1 → a ∩ b ∩ c ∈ S.Open1

export Twined3 (twined)

namespace Example_2_4_3
-- Not formalised
end Example_2_4_3

namespace Theorem_2_4_4

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

theorem t2' : .byzantine ≤ (⊡(S) f ∧ ⊡(S) f') → (⊨ (⟐(S) (f ∧ f'))) := by
  apply le_implies_valid t

end Theorem_2_4_4

namespace Corollary_2_4_5

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
  have x := Proposition_2_2_2.p9.mp (Theorem_2_4_4.t (f := ¬ᶠ f) (f' := ¬ᶠ f') (S := S))
  simpa [← Lemma_2_3_3.p1_2, Lemma_2_3_3.p1_5, Three.Lemmas.neg_and
        , Lemma_2_3_3.p1_6, Lemma_2_3_3.p1_6] using x

theorem t2 : ⊨ (⊡(S) (f ∨ f')) → ⊨ (⟐(S) f ∨ ⟐(S) f') := Three.Lemmas.le_implies_valid t1

end Corollary_2_4_5

namespace Remark_2_4_6

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
  : ⊨ (⊡(S) f) -> ⊡(S) f = Three.true := by
  intro h; simp [quorum, le_join] at h; obtain ⟨h1, h2, h3⟩ := h
  have ⟨qs, qm, p⟩ := q' q; simp
  refine ⟨qs ∩ h1, ?_, ?_⟩;
  have t := twined.twined qm qm h2; simpa using t
  intro x xq; obtain ⟨x1, x2⟩ := by simpa [Finset.mem_inter] using xq
  cases valid_TF.mp (p x x1); assumption
  next h => have := h3 _ x2; rw [h] at this; contradiction

include q in
theorem t2 [twined : Twined3 S] : ⊨ (⊡(S) f) -> ⊨ (T (⟐(S) f)) := by
  have h := Theorem_2_4_4.t (f := T ∘ f) (f' := T ∘ f) (S := S)
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
  le_implies_valid Theorem_2_4_4.t

omit q in
theorem t5_2 [twined : Twined3 S] : ⊨ (⊡(S) (f ∨ f')) → ⊨ (⟐(S) f ∨ ⟐(S) f') := by
  intro p; exact Corollary_2_4_5.t2 p

end Remark_2_4_6

namespace Remark_2_4_7

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
  specialize h (fun p => if p ∈ a then .true else .byzantine)
               (fun p => if p ∈ b then .true else .byzantine)
  have hqa : ⊡(S) (fun p => if p ∈ a then .true else .byzantine) = .true :=
    quorum_true.mpr ⟨a, ha, fun x hx => by simp [hx]⟩
  have hqb : ⊡(S) (fun p => if p ∈ b then .true else .byzantine) = .true :=
    quorum_true.mpr ⟨b, hb, fun x hx => by simp [hx]⟩
  rw [hqa, hqb] at h; simp at h
  obtain ⟨x, hxc, hx⟩ := h c hc
  have hxa : x ∈ a := by by_contra hna; simp [hna] at hx
  have hxb : x ∈ b := by by_contra hnb; simp [hnb] at hx
  exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hxa, hxb⟩, hxc⟩⟩

end Remark_2_4_7

section

variable
  {P : Type}
  [Fintype P]
  [Nonempty P]
  [DecidableEq P]
  {S : FinSemitopology P}
  {vote observe : P → 𝟯}

class ThyVote (S : FinSemitopology P) (vote observe : P → 𝟯) where
  observe? p : (observe p → ⊡(S) vote) = .true
  observe! p : (⊡(S) vote ⇀ observe p) = .true
  correct : ⊡(S) (TF ∘ vote) = .true
  observeN? p : (¬ (observe p) → ⊡(S) (¬ᶠ vote)) = .true
  observeN! p : (⊡(S) (¬ᶠ vote) ⇀ (¬ (observe p))) = .true
  twined3 f f' : (⊡(S) f ∧ ⊡(S) f') ≤ ⟐(S) (f ∧ f')

end

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
  rw [Proposition_2_2_2.p4]; intro h; obtain ⟨x, t⟩ := somewhere_true.mp h
  simp [quorum, le_join, le_meet]
  obtain ⟨s, xo, sp⟩ := by simpa [quorum] using mp_weak (i.observe? x) (byzantine_le.mpr (.inr t))
  refine ⟨_, xo, ?_⟩; intro y ys; simp [sp _ ys]

theorem t2 : ⊨ (⊡(S) vote ⇀ □ observe) := by
  rw [Proposition_2_2_2.p5, everywhere]; intro h;
  simp; intro p; exact mp_strong_true (i.observe! p) h

theorem t3 : ⊨ (◇ (¬ᶠ observe) → ⊡(S) (¬ᶠ vote)) := by
  rw [Proposition_2_2_2.p4]; intro h; obtain ⟨x, t⟩ := somewhere_true.mp h
  simp [quorum, le_join, le_meet]
  obtain ⟨s, xo, sp⟩ := by simpa [quorum] using mp_weak (i.observeN? x) (byzantine_le.mpr (.inr t))
  refine ⟨_, xo, ?_⟩; intro y ys; simp [sp _ ys]

theorem t4 : ⊨ (⊡(S) vote ⇀ □ observe) := by
  rw [Proposition_2_2_2.p5, everywhere]; intro h;
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
theorem t : ⊭ (◇ (T ∘ observe) ∧ ◇ (T ∘ (¬ᶠ observe))) := by
  apply notValid_by_contra
  intro h; rw [Valid, le_and] at h; have ⟨h1, h2⟩ := h
  simp [Remark_2_3_5.map_somewhere] at h1 h2
  have ⟨p, px⟩ := h1; have ⟨p', px'⟩ := h2
  have votep := mp_weak (i.observe? p) (byzantine_le.mpr (.inr px))
  have votep' := mp_weak (i.observeN? p') (by simp [px'])
  have q : (⊡(S) vote ∧ ⊡(S) (¬ᶠ vote)) = .true :=
    Three.Lemmas.and_true.mpr ⟨votep, votep'⟩
  have v : (⟐(S) (vote ∧ (¬ᶠ vote))) = .true := by
    have x := i.twined3 vote (¬ᶠ vote); simpa [q] using x
  rw [contraquorum, meet_true] at v
  have k : ⊨ (⟐(S) (B ∘ vote)) := by
    simp [contraquorum, le_meet]; intro s sm
    have ⟨y, ym, yp⟩ := join_true.mp (v _ sm)
    refine ⟨_, ym, ?_⟩
    simp [Three.Function.and] at yp
    apply Proposition_2_2_2.p7 (a := vote y) |>.mp
    simp [yp]
  have c : ⊡(S) (TF ∘ vote) = .true := i.correct
  have kc : ⊨ (⊡(S) (TF ∘ vote) ∧ (⟐(S) (B ∘ vote))) := by
    rw [Valid, le_and]; constructor; simp [c]; exact k
  have r := Lemma_2_3_7.c1 kc
  simp [somewhere, le_join] at r

end Proposition_2_5_7
