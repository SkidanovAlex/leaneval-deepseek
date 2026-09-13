import Mathlib

namespace Commons.Measure.Lebesgue

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution in
theorem ae_isVanishingPoint {n : ℕ} {ρ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure ρ]
    (hρ : ρ ⟂ₘ volume) :
    ∀ᵐ x ∂volume,
      Tendsto (fun r : ℝ => (ρ (ball x r)).toReal / r ^ n) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  -- Continuity of `ENNReal.toReal` at `0`.
  have htoReal : Tendsto ENNReal.toReal (𝓝 (0 : ℝ≥0∞)) (𝓝 0) := by
    simpa using ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) ENNReal.zero_ne_top
  -- The volume of the unit closed ball is a positive finite constant.
  have hcne : (volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_closedBall_pos volume 0 one_pos))
      (ne_of_lt (IsCompact.measure_lt_top (isCompact_closedBall 0 1)))
  -- Differentiation of the singular measure along the Besicovitch Vitali family.
  filter_upwards [VitaliFamily.ae_eventually_measure_zero_of_singular
      (Besicovitch.vitaliFamily (volume : Measure (EuclideanSpace ℝ (Fin n)))) hρ] with x hx
  have h1 : Tendsto (fun r : ℝ => ρ (closedBall x r) / volume (closedBall x r))
      (𝓝[>] (0:ℝ)) (𝓝 0) :=
    hx.comp (Besicovitch.tendsto_filterAt (volume : Measure (EuclideanSpace ℝ (Fin n))) x)
  have h2 : Tendsto (fun r : ℝ => (ρ (closedBall x r) / volume (closedBall x r)).toReal)
      (𝓝[>] (0:ℝ)) (𝓝 0) := htoReal.comp h1
  have h3 : Tendsto
      (fun r : ℝ => (volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal *
        (ρ (closedBall x r) / volume (closedBall x r)).toReal)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using h2.const_mul ((volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)
  -- Rewrite the density in terms of `r ^ n` using the volume of balls.
  have h4 : (fun r : ℝ => (volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal *
        (ρ (closedBall x r) / volume (closedBall x r)).toReal)
      =ᶠ[𝓝[>] (0:ℝ)] (fun r : ℝ => (ρ (closedBall x r)).toReal / r ^ n) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrp : (0:ℝ) < r := hr
    rw [ENNReal.toReal_div]
    have hW : (volume (closedBall x r)).toReal
        = r ^ n * (volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
      rw [← measureReal_def volume (closedBall x r),
        Measure.addHaar_real_closedBall' (volume : Measure (EuclideanSpace ℝ (Fin n))) x hrp.le,
        measureReal_def volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
        finrank_euclideanSpace, Fintype.card_fin]
    rw [hW]
    field_simp
  have h5 : Tendsto (fun r : ℝ => (ρ (closedBall x r)).toReal / r ^ n)
      (𝓝[>] (0:ℝ)) (𝓝 0) :=
    Tendsto.congr' h4 h3
  -- Conclude for open balls by monotonicity.
  refine squeeze_zero' ?_ ?_ h5
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonneg ENNReal.toReal_nonneg (pow_nonneg hr.le n)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    apply div_le_div_of_nonneg_right
    · exact ENNReal.toReal_mono
        (ne_of_lt ((measure_mono (subset_univ _)).trans_lt IsFiniteMeasure.measure_univ_lt_top))
        (measure_mono ball_subset_closedBall)
    · exact pow_nonneg hr.le n

end Commons.Measure.Lebesgue
