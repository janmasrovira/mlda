import Mathlib.Topology.Basic
-- import Mathlib.Data.Set.Finite.Basic
-- import Mathlib.Data.Set.Finite.Powerset
-- import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Defs
import Mathlib.Order.Basic
import Mathlib.Data.Finset.Fold

noncomputable
def Set.Finite.toList {A : Type} {K : Set A} (fin : K.Finite) : List {s | s ∈ K} :=
  have : Finite K := fin
  Fintype.ofFinite K |>.elems.toList
