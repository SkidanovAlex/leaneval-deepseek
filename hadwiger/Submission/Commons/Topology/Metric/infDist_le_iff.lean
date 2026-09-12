import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace Commons.Topology.Metric

theorem infDist_le_iff {E : Type*} [PseudoMetricSpace E] {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (x : E) (r : ℝ) :
    Metric.infDist x K ≤ r ↔ ∃ k ∈ K, dist x k ≤ r := by
  constructor
  · intro h
    obtain ⟨k, hk, hk'⟩ := hK.exists_infDist_eq_dist hne x
    exact ⟨k, hk, hk' ▸ h⟩
  · rintro ⟨k, hk, hkr⟩
    exact (Metric.infDist_le_dist_of_mem hk).trans hkr

end Commons.Topology.Metric