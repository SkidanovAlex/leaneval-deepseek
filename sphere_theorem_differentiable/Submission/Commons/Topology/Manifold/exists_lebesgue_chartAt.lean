import Mathlib.Geometry.Manifold.ChartedSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Topology.Manifold

/-- **Lebesgue number lemma for charts.** Given a continuous map `G : K → M` from a compact
(pseudo-)metric space into a charted space, there is a uniform `δ > 0` such that the image of every
ball of radius `δ` in `K` is contained in the source of a single chart of `M`. -/
theorem exists_lebesgue_chartAt
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {K : Type*} [PseudoMetricSpace K] [CompactSpace K] (G : K → M) (hG : Continuous G) :
    ∃ δ > 0, ∀ x : K, ∃ y : M, ∀ z : K, dist z x < δ → G z ∈ (chartAt H y).source := by
  have hcover : (Set.univ : Set K) ⊆ ⋃ y : M, G ⁻¹' (chartAt H y).source := by
    intro x _
    exact Set.mem_iUnion.2 ⟨G x, mem_chart_source H (G x)⟩
  have hopen : ∀ y : M, IsOpen (G ⁻¹' (chartAt H y).source) := fun y =>
    (chartAt H y).open_source.preimage hG
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hopen hcover
  exact ⟨δ, hδ, fun x => by
    obtain ⟨y, hy⟩ := hball x (Set.mem_univ x)
    exact ⟨y, fun z hz => hy (Metric.mem_ball.mpr hz)⟩⟩

end Commons.Topology.Manifold