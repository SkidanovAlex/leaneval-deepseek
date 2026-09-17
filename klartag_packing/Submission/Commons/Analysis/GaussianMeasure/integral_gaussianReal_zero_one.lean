import Mathlib.Probability.Distributions.Gaussian.Real

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory ProbabilityTheory

/-- The Gaussian measure with mean `0` and variance `1` has density
`(√(2π))⁻¹ * exp (-(x ^ 2 / 2))` with respect to the Lebesgue measure, so integrating any
function against it is the same as integrating it against that density. -/
theorem integral_gaussianReal_zero_one (f : ℝ → ℝ) :
    (∫ x : ℝ, f x ∂(ProbabilityTheory.gaussianReal 0 1))
      = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, f x * Real.exp (-(x ^ 2 / 2)) := by
  have hfun : ∀ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 1 x
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
    intro x
    simp only [ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    congr 1
    rw [neg_div]
  conv_lhs => rw [ProbabilityTheory.gaussianReal_of_var_ne_zero (0:ℝ) (by norm_num : (1 : NNReal) ≠ 0)]
  rw [integral_withDensity_eq_integral_toReal_smul (ProbabilityTheory.measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall (fun x => ProbabilityTheory.gaussianPDF_lt_top)) f]
  simp only [ProbabilityTheory.toReal_gaussianPDF, smul_eq_mul]
  simp_rw [hfun]
  rw [← integral_const_mul]
  congr 1
  ext x
  ring

end Commons.Analysis.GaussianMeasure