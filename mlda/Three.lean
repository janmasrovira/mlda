import Mathlib.Init
import Mathlib.Order.Basic
import Mathlib.Order.Fin.Basic

inductive Three : Type where
  | false
  | byzantine
  | true

notation "𝟯" => Three

namespace Three
namespace Atom

instance : LinearOrder Three := by
  let toFin : 𝟯 → Fin 3
    | .false => 0
    | .byzantine => 1
    | .true => 2
  apply LinearOrder.lift' toFin
  intro x y p
  cases x <;> cases y <;> cases p <;> rfl

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

@[simp]
def or : 𝟯 → 𝟯 → 𝟯
  | .false, .false => .false
  | .false, .byzantine => .byzantine
  | .byzantine, .false => .byzantine
  | .byzantine, .byzantine => .byzantine
  | _, _ => .true

scoped infixl:30 " ∨ " => or

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

def lift1 (op : 𝟯 → 𝟯) (f : X → 𝟯) : X → 𝟯 := op ∘ f
def lift2 (op : 𝟯 → 𝟯 → 𝟯) (f f' : X → 𝟯) : X → 𝟯 := fun x => op (f x) (f' x)

def and (f f' : X → 𝟯) : X → 𝟯 := lift2 Atom.and f f'
def or (f f' : X → 𝟯) : X → 𝟯 := lift2 Atom.or f f'
def impl (f f' : X → 𝟯) : X → 𝟯 := lift2 Atom.impl f f'
def strongImpl (f f' : X → 𝟯) : X → 𝟯 := lift2 Atom.strongImpl f f'

end Function
end Three
