import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace Commons.Probability.Gaussian

theorem stdGaussian_map_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    (ProbabilityTheory.stdGaussian E).map Neg.neg = ProbabilityTheory.stdGaussian E := by
  have h : (ProbabilityTheory.stdGaussian E).map (LinearIsometryEquiv.neg ℝ : E → E)
      = ProbabilityTheory.stdGaussian E :=
    ProbabilityTheory.stdGaussian_map (LinearIsometryEquiv.neg ℝ)
  rwa [LinearIsometryEquiv.coe_neg] at h

end Commons.Probability.Gaussian