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
scoped prefix:75 "¬" => neg

example : 𝟯 := ¬ Three.false

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

abbrev impl (a b : 𝟯) : 𝟯 := (¬ a) ∨ b
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

inductive Valid : 𝟯 → Prop where
  | true : Valid true
  | byzantine : Valid byzantine
scoped notation "⊨" => Valid

inductive NotValid : 𝟯 → Prop where
  | false : NotValid false
scoped notation "⊭" => NotValid

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

namespace Proposition_2_2_2

variable {a b : 𝟯}

@[simp] theorem p1_1 : ⊨ true := .true
@[simp] theorem p1_2 : ⊨ byzantine := .byzantine
@[simp] theorem p1_3 : ⊭ false := .false
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

theorem p3_1 : (a → b) = (¬ a ∨ b) := by cases a <;> cases b <;> rfl
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

variable {X : Type}

abbrev bigAnd (P : Finset X) (f : X → 𝟯) : 𝟯 := P.fold Atom.and true f
scoped notation "⋀" => bigAnd

def bigOr (P : Finset X) (f : X → 𝟯) : 𝟯 := P.fold Atom.or false f
scoped notation "⋁" => bigOr

@[simp] def lift1 (op : 𝟯 → 𝟯) (f : X → 𝟯) : X → 𝟯 := op ∘ f
@[simp] def lift2 (op : 𝟯 → 𝟯 → 𝟯) (f f' : X → 𝟯) : X → 𝟯 := fun x => op (f x) (f' x)

def neg (f : X → 𝟯) : X → 𝟯 := lift1 Atom.neg f
scoped prefix:75 "¬" => neg

def isNotByzantine (f : X → 𝟯) : X → 𝟯 := lift1 Atom.isNotByzantine f
scoped notation "TF" => isNotByzantine

theorem neg_fold {f : X → 𝟯} : (fun x => Atom.neg (f x)) = (¬ f) := by rfl

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

theorem false_or_byzantine_le (a : 𝟯) : (a = Three.false) ∨ .byzantine ≤ a := by cases a <;> decide

theorem true_or_le_byzantine (a : 𝟯) : (a = Three.true) ∨ a ≤ .byzantine := by cases a <;> decide

theorem neg_or : (¬ (a ∨ b)) = (¬ a ∧ ¬ b) := by
  cases a <;> cases b <;> simp!

theorem neg_and : (¬ (a ∧ b)) = (¬ a ∨ ¬ b) := by
  cases a <;> cases b <;> simp!

theorem Function.neg_and : (¬ (f ∧ f')) = (¬ f ∨ ¬ f') := by
  rw [Three.Function.and, Three.Function.or, Three.Function.neg]
  funext; apply Lemmas.neg_and

@[simp] theorem neg_neg : (¬ ¬ a) = a := by
  cases a <;> rfl

@[simp] theorem Function.neg_neg : (¬ (¬ f)) = f := by
  unfold Three.Function.neg; simp; funext a; rw [Function.comp, Function.comp]
  cases h : f a <;> rfl

theorem le_and : c ≤ (a ∧ b) ↔ (c ≤ a ∧ c ≤ b) := by
  cases a <;> cases b <;> cases c <;> decide

theorem and_le : (a ∧ b) ≤ c ↔ (a ≤ c ∨ b ≤ c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem and_true : (a ∧ b) = Three.true ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> decide

theorem and_byzantine : (a ∧ b) = Three.byzantine ↔ (a = byzantine ∧ byzantine ≤ b) ∨ (b = byzantine ∧ byzantine ≤ a) := by
  cases a <;> cases b <;> decide

theorem byzantine_le_and : Three.byzantine ≤ (a ∧ b) ↔ (byzantine ≤ a ∧ byzantine ≤ b) := by
  cases a <;> cases b <;> decide

theorem and_false : (a ∧ b) = Three.false ↔ (a = false ∨ b = false) := by
  cases a <;> cases b <;> decide

theorem or_true : (a ∨ b) = Three.true ↔ (a = true ∨ b = true) := by
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

@[simp] theorem meet_byzantine : ⋀ P f = byzantine ↔ (∀ x ∈ P, byzantine ≤ f x) ∧ ∃ x ∈ P, f x = byzantine := by
  unfold bigAnd;
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

@[simp] theorem meet_true : ⋀ P f = true ↔ ∀ x ∈ P, f x = true := by
  unfold bigAnd;
  have h : true ≤ P.fold min true f ↔ _ ∧ ∀ x ∈ P, true ≤ f x :=
    Finset.le_fold_min true
  simpa using h

@[simp] theorem join_false : ⋁ P f = false ↔ ∀ x ∈ P, f x = false := by
  unfold bigOr;
  have h : P.fold max false f ≤ false ↔ _ ∧ ∀ x ∈ P, f x ≤ false :=
    Finset.fold_max_le false
  simpa using h

theorem join_le_byzantine : ⋁ P f ≤ byzantine ↔ (∀ x ∈ P, f x ≤ byzantine) := by
  have h1 : P.fold max false f ≤ byzantine ↔ _ ∧ ∀ x ∈ P, f x ≤ byzantine :=
    Finset.fold_max_le byzantine
  simpa using h1

theorem byzantine_le_meet : byzantine ≤ ⋀ P f ↔ ∀ x ∈ P, f x ≥ byzantine := by
  have h2 : byzantine ≤ P.fold min true f ↔ _ ∧ ∀ x ∈ P, byzantine ≤ f x :=
    Finset.le_fold_min (f := f) byzantine
  simpa using h2

theorem byzantine_le_join : byzantine ≤ ⋁ P f ↔ ∃ x ∈ P, f x ≥ byzantine := by
  have h2 : byzantine ≤ P.fold max false f ↔ _ ∨ ∃ x ∈ P, f x ≥ byzantine :=
    Finset.le_fold_max byzantine
  simpa using h2

theorem le_meet : a ≤ ⋀ P f ↔ ∀ x ∈ P, a ≤ f x := by
  simpa using (Finset.le_fold_min (b := true) a)

theorem meet_le : ⋀ P f ≤ a ↔ a = true ∨ ∃ x ∈ P, f x ≤ a := by
  simpa using (Finset.fold_min_le (b := true) a)

theorem le_join : a ≤ ⋁ P f ↔ a = false ∨ ∃ x ∈ P, f x ≥ a := by
  simpa using (Finset.le_fold_max (b := false) a)

theorem join_le : ⋁ P f ≤ a ↔ ∀ x ∈ P, f x ≤ a := by
  simpa using (Finset.fold_max_le (b := false) a)

theorem join_byzantine : ⋁ P f = byzantine ↔ (∀ x ∈ P, f x ≤ byzantine) ∧ ∃ x ∈ P, f x = byzantine := by
  unfold bigOr;
  have h1 : P.fold max false f ≤ byzantine ↔ _ ∧ ∀ x ∈ P, f x ≤ byzantine :=
    Finset.fold_max_le byzantine
  have h2 : byzantine ≤ P.fold max false f ↔ _ ∨ ∃ x ∈ P, f x ≥ byzantine :=
    Finset.le_fold_max byzantine
  simp at h2 h1
  generalize P.fold Atom.or false f = y at *
  constructor
  rintro ⟨_⟩; constructor; simpa using h1; simp at h1 h2
  rcases h2 with ⟨u, mu, pu⟩; exists u; exists mu; exact (h1 u mu).antisymm pu
  rintro ⟨l, ⟨r, mr, pr⟩⟩; have p1 := h1.mpr l; have p2 := h2.mpr ⟨r, mr, ge_of_eq pr⟩
  exact p1.antisymm p2

@[simp] theorem join_true : ⋁ P f = true ↔ ∃ x ∈ P, f x = true := by
  unfold bigOr;
  have h : true ≤ P.fold max false f ↔ _ ∨ ∃ x ∈ P, true ≤ f x :=
    Finset.le_fold_max true
  simpa using h

theorem meet_neg : ⋀ P (¬ f) = ¬ ⋁ P f := by
  have := Finset.fold_hom (op := Atom.or) (op' := Atom.and) (b := false) (f := f) (m := Atom.neg) (s := P) ?_
  simp at this; exact this; apply neg_or

theorem join_neg : ⋁ P (¬ f) = ¬ ⋀ P f := by
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

theorem valid_TF : ⊨ (TF a) ↔ a = true ∨ a = false := by
  constructor <;> intro h <;> cases a <;> cases h <;> first | contradiction | simp

@[simp] theorem valid_T : ⊨ (T a) ↔ a = true := by
  constructor <;> intro h <;> cases a <;> cases h <;> simp

theorem valid_cases : ⊨ a ↔ a = true ∨ a = byzantine := by cases a <;> simp

theorem valid_byzantine_le : ⊨ a ↔ byzantine ≤ a := by cases a <;> simp

@[simp] theorem byzantine_le_T : .byzantine ≤ T a ↔ a = true := by cases a <;> simp
end Lemmas

end Three
