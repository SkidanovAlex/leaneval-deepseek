import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace Commons.Probability.Gaussian

/-- The standard Gaussian measure on a finite-dimensional real inner product space is invariant
under negation. -/
private theorem stdGaussian_map_neg_aux {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    (ProbabilityTheory.stdGaussian E).map Neg.neg = ProbabilityTheory.stdGaussian E := by
  have h := ProbabilityTheory.stdGaussian_map (E := E) (LinearIsometryEquiv.neg ℝ)
  simpa using h

theorem prod_stdGaussian_map_neg_snd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ((ProbabilityTheory.stdGaussian E).prod (ProbabilityTheory.stdGaussian E)).map
        (fun p : E × E => (p.1, -p.2))
      = (ProbabilityTheory.stdGaussian E).prod (ProbabilityTheory.stdGaussian E) := by
  have hmap : (fun p : E × E => (p.1, -p.2)) = Prod.map id Neg.neg := rfl
  rw [hmap, ← MeasureTheory.Measure.map_prod_map (ProbabilityTheory.stdGaussian E)
        (ProbabilityTheory.stdGaussian E) measurable_id measurable_neg]
  rw [MeasureTheory.Measure.map_id, stdGaussian_map_neg_aux]

end Commons.Probability.Gaussian