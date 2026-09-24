import Mathlib

open MeasureTheory

namespace Work.GM.Affine

set_option linter.unusedVariables false

/-- The parametric integral `u ↦ ∫ t in S, φ u t * w t` is interval-integrable on `(0,1]` under
the same hypotheses as `Work.GM.Affine.pair_swap` (joint continuity, `φ` bounded by `D` on
`[0,1] × ℝ`, `w` integrable on `S`).  This is what makes `intervalIntegral.integral_mono_on`
applicable to a pointwise inequality in `u`. -/
theorem intervalIntegrable_parametric {S : Set ℝ} (hS : MeasurableSet S) {φ : ℝ → ℝ → ℝ}
    {w : ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hcont : Continuous (fun p : ℝ × ℝ => φ p.1 p.2 * w p.2))
    (hwint : MeasureTheory.IntegrableOn w S volume)
    (hbdd : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ t, ‖φ u t‖ ≤ D) :
    IntervalIntegrable (fun u => ∫ t in S, φ u t * w t) volume (0 : ℝ) 1 := by
  -- For every `u`, the map `t ↦ φ u t * w t` is continuous, hence a.e. strongly measurable.
  have hmeas : ∀ u : ℝ,
      AEStronglyMeasurable (fun t : ℝ => φ u t * w t) (volume.restrict S) := by
    intro u
    have h : Continuous (fun t : ℝ => φ u t * w t) :=
      hcont.comp (continuous_const.prodMk continuous_id)
    exact h.stronglyMeasurable.aestronglyMeasurable
  -- The dominating function `t ↦ D * ‖w t‖` is integrable on `S`.
  have hbound_int : Integrable (fun t : ℝ => D * ‖w t‖) (volume.restrict S) :=
    (MeasureTheory.IntegrableOn.integrable hwint).norm.const_mul D
  -- The family is dominated, uniformly in `u ∈ [0,1]`, by `D * ‖w ·‖`.
  have hbound : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ t ∂volume.restrict S, ‖φ u t * w t‖ ≤ D * ‖w t‖ :=
    fun u hu => Filter.Eventually.of_forall (fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbdd u hu t) (norm_nonneg _))
  -- For every `t`, the map `u ↦ φ u t * w t` is continuous.
  have hcont_on : ∀ᵐ t ∂volume.restrict S,
      ContinuousOn (fun u : ℝ => φ u t * w t) (Set.Icc 0 1) :=
    Filter.Eventually.of_forall (fun t =>
      (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn)
  -- Dominated convergence in the parameter `u`.
  have hF_cont : ContinuousOn (fun u => ∫ t, φ u t * w t ∂volume.restrict S)
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_of_dominated (fun u _ => hmeas u) hbound hbound_int hcont_on
  exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hF_cont

end Work.GM.Affine
