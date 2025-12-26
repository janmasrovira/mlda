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

@[simp]
def neg : 𝟯 → 𝟯
  | .false => .true
  | .byzantine => .byzantine
  | .true => .false
scoped prefix:75 "¬" => neg

example : 𝟯 := ¬ Three.false

@[simp]
def and : 𝟯 → 𝟯 → 𝟯
  | .true, .true => .true
  | .byzantine, .true => .byzantine
  | .true, .byzantine => .byzantine
  | .byzantine, .byzantine => .byzantine
  | _, _ => .false

scoped infixl:35 " ∧ " => and

instance : Std.Associative and where
  assoc := by intro a b c; cases a <;> cases b <;> cases c <;> simp

instance : Std.Commutative and where
  comm := by intro a b; cases a <;> cases b <;> simp

instance : Std.LawfulCommIdentity and .true where
  left_id := by intro a; cases a <;> simp

@[simp]
def or : 𝟯 → 𝟯 → 𝟯
  | .false, .false => .false
  | .false, .byzantine => .byzantine
  | .byzantine, .false => .byzantine
  | .byzantine, .byzantine => .byzantine
  | _, _ => .true

scoped infixl:30 " ∨ " => or

instance : Std.Associative or where
  assoc := by intro a b c; cases a <;> cases b <;> cases c <;> simp

instance : Std.Commutative or where
  comm := by intro a b; cases a <;> cases b <;> simp

instance : Std.LawfulCommIdentity or .false where
  left_id := by intro a; cases a <;> simp

@[simp]
def xor : 𝟯 → 𝟯 → 𝟯
  | .byzantine, _ => .byzantine
  | _, .byzantine => .byzantine
  | .true, .true => .false
  | .false, .false => .false
  | _, _ => .true

scoped infixl:30 " ⊕ " => xor

@[simp]
def impl (a b : 𝟯) : 𝟯 := (¬ a) ∨ b

scoped infixl:25 " → " => impl

@[simp]
def isTrue : 𝟯 → 𝟯
 | .true => .true
 | _ => .false
scoped notation "T" => isTrue

@[simp]
def isByzantine : 𝟯 → 𝟯
 | .byzantine => .true 
 | _ => .false
scoped notation "B" => isByzantine

@[simp]
def isFalse : 𝟯 → 𝟯
 | .false => .true 
 | _ => .false
scoped notation "F" => isFalse

@[simp]
def isNotFalse : 𝟯 → 𝟯
 | .false => .false 
 | _ => .true
scoped notation "TB" => isNotFalse

@[simp]
def isNotByzantine : 𝟯 → 𝟯
 | .byzantine => .false 
 | _ => .true
scoped notation "TF" => isNotByzantine

@[simp]
def strongImpl (a b : 𝟯) : 𝟯 := a → T b

scoped infixl:25 " ⇀ " => strongImpl

inductive Valid : 𝟯 → Prop where
  | true : Valid .true
  | byzantine : Valid .byzantine
scoped notation "⊨" => Valid

inductive NotValid : 𝟯 → Prop where
  | false : NotValid .false
scoped notation "⊭" => NotValid

instance : Ord 𝟯 where
  compare := fun
   | .false, .false => .eq
   | .false, _ => .lt
   | _, .false => .gt
   | .byzantine, .byzantine => .eq
   | .byzantine, .true => .lt
   | .true, .byzantine => .gt
   | .true, .true => .eq

instance : LinearOrder Three := by
  let toFin : 𝟯 → Fin 3
    | .false => 0
    | .byzantine => 1
    | .true => 2
  apply LinearOrder.liftWithOrd' toFin
  intro x y p; cases x <;> cases y <;> cases p <;> rfl
  intro x y; cases x <;> cases y <;> rfl

instance : BoundedOrder Three where
  bot := .false
  bot_le := by intro a; cases a <;> decide
  top := .true
  le_top := by intro a; cases a <;> decide

instance : DistribLattice Three where
  le_sup_inf := by intro a b c; cases a <;> cases b <;> cases c <;> decide

namespace Proposition_2_2_2

variable (a b : 𝟯)

@[simp] theorem p1_1 : ⊨ .true := .true
@[simp] theorem p1_2 : ⊨ .byzantine := .byzantine
@[simp] theorem p1_3 : ⊭ .false := .false
@[simp] theorem p1_4 : ¬ (⊨ .false) := by intro k; cases k
@[simp] theorem p1_5 : ¬ (⊭ .true) := by intro k; cases k
@[simp] theorem p1_6 : ¬ (⊭ .byzantine) := by intro k; cases k

theorem p2_1 : ⊨ (a ∨ b) ↔ ⊨ a ∨ ⊨ b := by
  constructor <;> intro x
  next => cases a <;> cases b <;> cases x <;> simp
  next => cases x <;> rename_i k <;> cases a <;> cases b <;> cases k <;> simp

theorem p2_2 : ⊨ (a ∧ b) ↔ ⊨ a ∧ ⊨ b := by
  constructor <;> intro x
  next => cases a <;> cases b <;> cases x <;> simp
  next => rcases x with ⟨k1, k2⟩; cases a <;> cases b <;> cases k1 <;> cases k2 <;> simp

theorem p3_1 : (a → b) = (¬ a ∨ b) := by cases a <;> cases b <;> rfl
theorem p3_2 : (a ⇀ b) = (a → T b) := by cases a <;> cases b <;> rfl

theorem p4 : ⊨ (a → b) ↔ ((a = .true) → ⊨ (TB b)) := by
  constructor <;> cases a <;> cases b <;> simp

theorem p5 : ⊨ (a ⇀ b) ↔ ((a = .true) → (b = .true)) := by
  constructor <;> cases a <;> cases b <;> simp

theorem p6 : ⊨ (a ∨ ¬ a) := by cases a <;> simp

theorem p7 : ⊨ (a ∧ ¬ a) ↔ a = .byzantine := by
  constructor <;> cases a <;> simp

theorem p8 : ⊨ a ↔ (TF a = T a) := by cases a <;> simp

theorem p9 : a ≤ b ↔ ((¬ b) ≤ ¬ a) := by
  constructor <;> cases a <;> cases b <;> decide

end Proposition_2_2_2

end Atom

namespace Function

variable {X : Type}

def bigAnd (f : X → 𝟯) (P : Finset X) : 𝟯 := P.fold Atom.and .true f
scoped notation "⋀" => bigAnd

def bigOr (f : X → 𝟯) (P : Finset X) : 𝟯 := P.fold Atom.or .false f
scoped notation "⋁" => bigOr

@[simp] def lift1 (op : 𝟯 → 𝟯) (f : X → 𝟯) : X → 𝟯 := op ∘ f
@[simp] def lift2 (op : 𝟯 → 𝟯 → 𝟯) (f f' : X → 𝟯) : X → 𝟯 := fun x => op (f x) (f' x)

@[simp] def neg (f : X → 𝟯) : X → 𝟯 := lift1 Atom.neg f
scoped prefix:75 "¬" => neg

@[simp] def and (f f' : X → 𝟯) : X → 𝟯 := lift2 Atom.and f f'
scoped infixl:35 " ∧ " => and

@[simp] def or (f f' : X → 𝟯) : X → 𝟯 := lift2 Atom.or f f'
scoped infixl:30 " ∨ " => or

def impl (f f' : X → 𝟯) : X → 𝟯 := lift2 Atom.impl f f'
def strongImpl (f f' : X → 𝟯) : X → 𝟯 := lift2 Atom.strongImpl f f'

end Function

namespace Lemmas

open scoped Three.Function
open Three.Function

variable {X : Type} (P : Finset X) (a : 𝟯) (f : X → 𝟯)

@[simp] theorem minr : min = Atom.and := by
  funext a b; cases a <;> cases b <;> rfl

@[simp] theorem maxr : max = Atom.or := by
  funext a b; cases a <;> cases b <;> rfl

@[simp] theorem le_bot : a ≤ .false ↔ a = .false := by
  constructor <;> (intro p; cases a; rfl; contradiction; contradiction )

@[simp] theorem top_le : .true ≤ a ↔ a = .true := by
  constructor <;> (intro p; cases a; contradiction; contradiction; rfl)

@[simp] theorem meet_false : ⋀ f P = false ↔ ∃ x ∈ P, f x = false := by
  unfold bigAnd; constructor;
  intro h
  have k : Finset.fold min true f P ≤ false := by simp [h]
  have k1 := (Finset.fold_min_le false).mp k; simpa using k1
  rintro ⟨u, pu, pu2⟩
  have h' : ∃ x ∈ P, f x ≤ false := ⟨u, pu, (le_bot (f u)).mpr pu2⟩
  have k1 := (Finset.fold_min_le false).mpr (.inr (a := true ≤ false) h')
  simpa using k1

@[simp] theorem join_true : ⋁ f P = .true ↔ ∃ x ∈ P, f x = .true := by
  unfold bigOr; constructor;
  intro h
  have k : true ≤ Finset.fold max false f P := by simp [h]
  have k1 := (Finset.le_fold_max true).mp k; simpa using k1
  rintro ⟨u, pu, pu2⟩
  have h' : ∃ x ∈ P, true ≤ f x := ⟨u, pu, (top_le (f u)).mpr pu2⟩
  have k1 := (Finset.le_fold_max true).mpr (.inr (a := .true ≤ Three.false) h')
  simpa using k1

end Lemmas


end Three
