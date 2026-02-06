import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Basic
import Mathlib.Topology.Basic

class MapMin {A : Type} [Min A] (op : A → A) where
  map_min : ∀ x y, op (min x y) = min (op x) (op y)

export MapMin (map_min)

class MapMax {A : Type} [Max A] (op : A → A) where
  map_max : ∀ x y, op (max x y) = max (op x) (op y)

export MapMax (map_max)

-- theorem fold_max_top {α β} [LinearOrder β] [BoundedOrder β] [DecidableEq α] {s : Finset α} {f : α → β} {b : β}
--   : Finset.fold max b f s = Top.top ↔ b = Top.top ∨ ∃ a, f a = Top.top := by
--   have := Finset.le_fold_max (s := s) (f := f) (b := b) Top.top





