import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Integral

namespace Commons.MeasureTheory.Integral

/-- The function `x ↦ ‖x‖ ^ 2` is convex on a real normed space: the norm itself is convex and
nonnegative, and `t ↦ t ^ 2` is convex and increasing on `[0, ∞)`. -/
theorem convexOn_univ_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ConvexOn ℝ (Set.univ : Set E) (fun y : E => ‖y‖ ^ 2) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h1 : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have h2 : (0 : ℝ) ≤ ‖a • x + b • y‖ := norm_nonneg _
  have h4 : ‖a • x + b • y‖ ^ 2 ≤ (a * ‖x‖ + b * ‖y‖) ^ 2 :=
    pow_le_pow_left₀ h2 h1 2
  have h5 : (a * ‖x‖ + b * ‖y‖) ^ 2 ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), mul_nonneg ha hb, hab]
  simpa [smul_eq_mul] using h4.trans h5

/-- Jensen's inequality in the form needed for `L²` energy estimates: for a probability measure
`μ` and a Bochner integrable `g`, the square of the norm of the mean of `g` is at most the mean of
the square of the norm.  (Convexity of `x ↦ ‖x‖ ^ 2` plus `ConvexOn.map_integral_le`.) -/
theorem norm_integral_sq_le_integral_norm_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ] {g : α → E}
    (hg : MeasureTheory.Integrable g μ)
    (hg2 : MeasureTheory.Integrable (fun x => ‖g x‖ ^ 2) μ) :
    ‖∫ x, g x ∂μ‖ ^ 2 ≤ ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have hcont : ContinuousOn (fun y : E => ‖y‖ ^ 2) Set.univ :=
    (continuous_norm.pow 2).continuousOn
  have key := (convexOn_univ_norm_sq (E := E)).map_integral_le hcont isClosed_univ
    (by simp) hg hg2
  simpa using key

end Commons.MeasureTheory.Integral