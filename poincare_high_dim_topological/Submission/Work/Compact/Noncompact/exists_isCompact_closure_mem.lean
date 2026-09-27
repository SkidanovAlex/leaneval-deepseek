import Mathlib

namespace Work.Compact.Noncompact

/-- Every point of a topological manifold modelled on `ℝⁿ` has an open neighbourhood whose
closure is compact: the model space `ℝⁿ` is locally compact, hence so is `M` (by
`ChartedSpace.locallyCompactSpace`), and in a Hausdorff space a compact neighbourhood of a point
contains the closure of an open neighbourhood of that point. -/
theorem exists_isCompact_closure_mem {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ IsCompact (closure U) := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨V, hVK, hVo, hxV⟩ := mem_nhds_iff.mp hKx
  exact ⟨V, hVo, hxV,
    hK.of_isClosed_subset isClosed_closure (hK.isClosed.closure_subset_iff.mpr hVK)⟩

end Work.Compact.Noncompact
