import Mathlib.Topology.Basic

structure Semitopology {A : Type} [TopologicalSpace A] (P : Set A) where
  Open : Set (Set A)
  open_sets : ∀ {O : Set A}, O ∈ Open → IsOpen O
  in_P : ∀ {O : Set A}, O ∈ Open → O ⊆ P
  closed_unions : ∀ {S : Set (Set A)}, S ⊆ Open → ⋃₀ S ∈ Open
