import Mathlib

namespace Work.Mostow

theorem integrable_inner_mul {n : ℕ} (ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
    [MeasureTheory.IsProbabilityMeasure ν]
    (hsupp : ν (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)ᶜ = 0)
    (v w : EuclideanSpace ℝ (Fin n)) :
    MeasureTheory.Integrable (fun ξ => (inner ℝ ξ v) * (inner ℝ ξ w)) ν := by
  -- ν-almost every ξ lies on the unit sphere, hence ‖ξ‖ = 1
  have hnorm : ∀ᵐ ξ ∂ν, ‖ξ‖ = 1 := by
    have hsphere : ∀ᵐ ξ ∂ν, ξ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      rw [MeasureTheory.ae_iff]
      exact hsupp
    filter_upwards [hsphere] with ξ hξ
    rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hξ
  -- the integrand is continuous, hence strongly measurable
  refine MeasureTheory.Integrable.of_bound ?_ (‖v‖ * ‖w‖) ?_
  · exact (continuous_id.inner continuous_const).mul
      (continuous_id.inner continuous_const) |>.aestronglyMeasurable
  · -- and it is bounded by ‖v‖ * ‖w‖ almost everywhere
    filter_upwards [hnorm] with ξ hξ
    rw [norm_mul]
    calc ‖inner ℝ ξ v‖ * ‖inner ℝ ξ w‖
        ≤ (‖ξ‖ * ‖v‖) * (‖ξ‖ * ‖w‖) := by
          gcongr <;> exact norm_inner_le_norm _ _
      _ = ‖v‖ * ‖w‖ := by rw [hξ]; ring

end Work.Mostow
