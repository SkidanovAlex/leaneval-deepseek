import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Lattice.Discrete

/-- A subgroup (submodule) of a discrete subgroup of a topological group is itself discrete:
the subspace topology induced on a subset of a discrete set is discrete. -/
lemma discreteTopology_of_le {n : ℕ} {ℒ ℒ' : Submodule ℤ (EuclideanSpace ℝ (Fin n))} (hle : ℒ' ≤ ℒ) [DiscreteTopology ℒ] :
    DiscreteTopology ℒ' := by
  let s : Set (EuclideanSpace ℝ (Fin n)) := ℒ
  let t : Set (EuclideanSpace ℝ (Fin n)) := ℒ'
  have hts : t ⊆ s := hle
  have hDs : DiscreteTopology s := by
    change DiscreteTopology ℒ
    infer_instance
  exact DiscreteTopology.of_subset (s := s) (t := t) hDs hts

end Commons.Lattice.Discrete