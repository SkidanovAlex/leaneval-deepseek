import Mathlib.Topology.Compactness.Compact

universe u

namespace Commons.Topology.Compactness

theorem finite_of_isCompact_of_isolated {X : Type u} [TopologicalSpace X] {s : Set X}
    (hs : IsCompact s) (hiso : ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ U ∩ s = {x}) :
    s.Finite := by
  -- For each x ∈ s pick an open neighbourhood that isolates x inside s.
  let U : s → Set X := fun x => Classical.choose (hiso x.1 x.2)
  have hUo : ∀ x : s, IsOpen (U x) := by
    intro x
    exact (Classical.choose_spec (hiso x.1 x.2)).1
  have hU : ∀ x : s, U x ∩ s = {x.1} := by
    intro x
    exact (Classical.choose_spec (hiso x.1 x.2)).2
  -- The family {U x : x ∈ s} is an open cover of s.
  have hcov : s ⊆ ⋃ x : s, U x := by
    intro y hy
    refine Set.mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
    have hyU : y ∈ U ⟨y, hy⟩ := by
      have hyUin : y ∈ U ⟨y, hy⟩ ∩ s := by
        rw [hU ⟨y, hy⟩]
        simp
      exact hyUin.1
    exact hyU
  -- Compactness gives a finite subcover indexed by t : Finset s.
  rcases hs.elim_finite_subcover U hUo hcov with ⟨t, hsub⟩
  -- Every point of s covered by U i (i ∈ t) equals i itself, so s lies in
  -- the (finite) image of the finite set t under the subtype embedding.
  have hsub' : s ⊆ (fun x : s => (x : X)) '' (↑t : Set s) := by
    intro y hy
    have hyU : y ∈ ⋃ i ∈ t, U i := hsub hy
    rcases Set.mem_iUnion.mp hyU with ⟨i, hiU⟩
    rcases Set.mem_iUnion.mp hiU with ⟨hit, hyUi⟩
    have hyin : y ∈ U i ∩ s := ⟨hyUi, hy⟩
    have hyeq : y = (i : X) := by
      rw [hU i] at hyin
      simpa using hyin
    refine ⟨i, ?_, ?_⟩
    · exact Finset.mem_coe.mpr hit
    · exact hyeq.symm
  exact Set.Finite.subset
    (Set.Finite.image (fun x : s => (x : X)) (Finset.finite_toSet t)) hsub'

end Commons.Topology.Compactness