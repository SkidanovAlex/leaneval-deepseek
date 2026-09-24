import Mathlib

/-!
# The `hint` bookkeeping of the chamber engine

`Commons.Topology.Homotopy.deformationRetract_of_chamber_folds` requires, for an `ℕ`-indexed family
of chambers `c` and a subspace `S`,

`hint : ∀ x, ∃ n, x ∈ interior ((⋃ i ∈ Finset.range n, closure (c i)) ∪ S)`.

This file proves that this is automatic as soon as the family is locally finite and covers the
space (no surjectivity/reindexing is needed — the only point is that at a fixed `x` the locally
finite family has only finitely many members meeting a neighbourhood, and a large enough initial
segment of the enumeration contains all of them).
-/

open Set Filter
open scoped Topology

namespace Commons.Topology.Connected

theorem interior_closure_cover_of_locallyFinite {X : Type*} [TopologicalSpace X] (C : ℕ → Set X)
    (hlf : LocallyFinite C) (hcov : ∀ x : X, x ∈ ⋃ n, C n) (S : Set X) :
    ∀ x : X, ∃ n : ℕ, x ∈ interior ((⋃ i ∈ Finset.range n, closure (C i)) ∪ S) := by
  intro x
  obtain ⟨t, ht, hfin⟩ := hlf x
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N + 1, ?_⟩
  have hsub : t ⊆ (⋃ i ∈ Finset.range (N + 1), closure (C i)) ∪ S := by
    intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov y)
    have hjn : j ∈ {i : ℕ | (C i ∩ t).Nonempty} := ⟨y, hj, hy⟩
    refine Or.inl (mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr ?_, subset_closure hj⟩)
    exact Nat.lt_succ_of_le (hN hjn)
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset ht hsub)

end Commons.Topology.Connected
