import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace Commons.Analysis.GaussianMeasure

theorem gaussian_total_mass_one (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    (∫ x : E, Real.exp (-Real.pi * ‖x‖ ^ 2)) = 1 := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (show (0 : ℝ) < Real.pi from Real.pi_pos)]
  have hdiv : Real.pi / Real.pi = (1 : ℝ) := div_self (ne_of_gt Real.pi_pos)
  rw [hdiv]
  exact Real.one_rpow _

end Commons.Analysis.GaussianMeasure