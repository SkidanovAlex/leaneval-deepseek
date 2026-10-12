import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxBridge.Resolve

/-- The kinetic kernel `K_F(z) = (2π)⁻³∫_p F(‖p‖)cos⟪p,z⟫dp` is bounded by the (normalised)
`L¹` norm of the radial symbol: taking absolute values inside the `p`-integral and using
`|cos| ≤ 1` gives `‖K_F(z)‖ ≤ (2π)⁻³∫_p ‖F(‖p‖)‖dp`, uniformly in `z`. -/
theorem kinKernel_bdd (F : ℝ → ℝ)
    (hF : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (z : EuclideanSpace ℝ (Fin 3)) :
    ‖Submission.BoseGases.kinKernel F z‖ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
      ∫ p : EuclideanSpace ℝ (Fin 3), ‖F ‖p‖‖ := by
  have hc : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  have hb : ‖∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ * Real.cos (inner ℝ p z)‖ ≤
      ∫ p : EuclideanSpace ℝ (Fin 3), ‖F ‖p‖‖ := by
    apply MeasureTheory.norm_integral_le_of_norm_le hF.norm
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [Submission.BoseGases.kinKernel, norm_mul, Real.norm_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left hb hc

end Work.SmallBoxBridge.Resolve
