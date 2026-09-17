import Mathlib
import Submission.Commons.Topology.MetricSpace.sphere_net_cardinality

namespace Commons.Topology.MetricSpace

/-- In `ℝ^d` (as `EuclideanSpace ℝ (Fin d)`) the unit sphere has, for every `0 < δ ≤ 1`,
a finite `δ`-net made of unit vectors, whose cardinality is at most `(C/δ)^d` for a
universal constant `C ≥ 1` (here `C = 3`).

The construction takes the finite net produced by `sphere_net_cardinality` (a maximal
`δ`-separated subset of the sphere, which is finite by compactness) and turns it into a
`Finset`. -/
theorem exists_finset_sphere_net (d : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin d)), (∀ x ∈ S, ‖x‖ = 1) ∧
      (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ δ) ∧
      ∃ C : ℝ, 1 ≤ C ∧ (S.card : ℝ) ≤ (C / δ) ^ d := by
  obtain ⟨C, hC1, hmain⟩ := sphere_net_cardinality
  obtain ⟨S, hSfin, hSnorm, hSnet, hSbound⟩ := hmain d δ hδ0 hδ1
  refine ⟨hSfin.toFinset, ?_, ?_, C, hC1, ?_⟩
  · intro x hx
    exact hSnorm x ((Set.Finite.mem_toFinset hSfin).mp hx)
  · intro y hy
    obtain ⟨x, hxS, hxy⟩ := hSnet y hy
    exact ⟨x, (Set.Finite.mem_toFinset hSfin).mpr hxS, hxy⟩
  · simpa [Set.ncard_eq_toFinset_card S hSfin] using hSbound

end Commons.Topology.MetricSpace
