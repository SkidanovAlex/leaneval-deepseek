import Mathlib
import Submission.Work.CoreTopology.TorusDichotomyDefs

namespace Work.CoreTopology

/-- The horizontal projection of a point of the standard torus is
`(2 + cos φ) · exp (i θ)`. -/
theorem horizVec_torusMap_eq (θ φ : ℝ) :
    horizVec (Work.Core.torusMap θ φ) =
      (((2 + Real.cos φ : ℝ)) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext <;>
    simp [horizVec, Work.Core.torusMap, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- The norm of the horizontal projection of a point of the standard torus is
`2 + cos φ`, which is positive. -/
theorem norm_horizVec_torusMap (θ φ : ℝ) :
    ‖horizVec (Work.Core.torusMap θ φ)‖ = 2 + Real.cos φ := by
  have hc : (0 : ℝ) < 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
  rw [horizVec_torusMap_eq θ φ, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [this, mul_one]

/-- **The normalised horizontal projection of a point of the standard torus is `exp (i θ)`.**
For all `θ φ`, `horizVec (torusMap θ φ) / ‖horizVec (torusMap θ φ)‖ = exp (i θ)`, since the
horizontal projection is `(2 + cos φ) · exp (i θ)` and `2 + cos φ > 0`. -/
theorem horizVec_torusMap_div_norm (θ φ : ℝ) :
    horizVec (Work.Core.torusMap θ φ) / ((‖horizVec (Work.Core.torusMap θ φ)‖ : ℝ) : ℂ) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
  have hc : (0 : ℝ) < 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
  rw [norm_horizVec_torusMap θ φ, horizVec_torusMap_eq θ φ]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hc))

end Work.CoreTopology
