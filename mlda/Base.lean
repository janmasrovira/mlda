import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Defs
import Mathlib.Order.Basic
import Mathlib.Topology.Basic

class MapMin {A : Type} [Min A] (op : A → A) where
  map_min : ∀ x y, op (min x y) = min (op x) (op y)

export MapMin (map_min)

class MapMax {A : Type} [Max A] (op : A → A) where
  map_max : ∀ x y, op (max x y) = max (op x) (op y)

export MapMax (map_max)

section

def ExistsAffine.{u} {α : Sort u} (p : α → Prop) : Prop := {a b : α} → p a → p b → a = b
notation " ∃? " => ExistsAffine
notation "∃? " x ", " p => ExistsAffine (fun x => p)

end
