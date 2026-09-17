import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace Commons.Probability.Gaussian

/-- For the standard Gaussian measure on a finite-dimensional real inner product space,
the second mixed moment of two linear functionals `z ↦ ⟪u, z⟫` and `z ↦ ⟪v, z⟫` is the
inner product `⟪u, v⟫`. -/
theorem integral_inner_mul_inner_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u v : E) :
    ∫ z, (inner ℝ u z) * (inner ℝ v z) ∂(ProbabilityTheory.stdGaussian E) = inner ℝ u v := by
  have hmem : MeasureTheory.MemLp id 2 (ProbabilityTheory.stdGaussian E) :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  rw [show (∫ z, (inner ℝ u z) * (inner ℝ v z) ∂(ProbabilityTheory.stdGaussian E))
      = ∫ z, (inner ℝ u (z - ∫ x, id x ∂(ProbabilityTheory.stdGaussian E)))
              * (inner ℝ v (z - ∫ x, id x ∂(ProbabilityTheory.stdGaussian E)))
            ∂(ProbabilityTheory.stdGaussian E) by
        simp [ProbabilityTheory.integral_id_stdGaussian]]
  rw [← ProbabilityTheory.covarianceBilin_apply (μ := ProbabilityTheory.stdGaussian E) hmem u v,
    ProbabilityTheory.covarianceBilin_stdGaussian]
  rfl

end Commons.Probability.Gaussian