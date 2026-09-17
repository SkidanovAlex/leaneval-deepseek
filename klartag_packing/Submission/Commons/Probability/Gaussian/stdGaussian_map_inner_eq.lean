import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace Commons.Probability.Gaussian

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem stdGaussian_map_inner_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (w : E) : (ProbabilityTheory.stdGaussian E).map (fun z : E => inner ℝ z w) = (ProbabilityTheory.stdGaussian ℝ).map (fun y : ℝ => ‖w‖ * y) := by
  have hstd : (ProbabilityTheory.stdGaussian ℝ) = ProbabilityTheory.gaussianReal 0 1 := by
    rw [ProbabilityTheory.IsGaussian.eq_gaussianReal (ProbabilityTheory.stdGaussian ℝ)
      (ProbabilityTheory.isGaussian_stdGaussian (E := ℝ))]
    have h1 : (ProbabilityTheory.stdGaussian ℝ)[id] = 0 := by
      simp
    have h2 : Var[id; ProbabilityTheory.stdGaussian ℝ] = 1 := by
      have h := ProbabilityTheory.variance_dual_stdGaussian (E := ℝ)
        (L := ContinuousLinearMap.id ℝ ℝ)
      simpa using h
    rw [h1, h2]
    norm_num
  have hL : (ProbabilityTheory.stdGaussian E).map (innerSL ℝ w)
      = ProbabilityTheory.gaussianReal 0 ((‖w‖ ^ 2).toNNReal) := by
    rw [ProbabilityTheory.IsGaussian.map_eq_gaussianReal (L := innerSL ℝ w),
      ProbabilityTheory.integral_strongDual_stdGaussian,
      ProbabilityTheory.variance_dual_stdGaussian, innerSL_apply_norm]
  have hR : (ProbabilityTheory.stdGaussian ℝ).map (fun y : ℝ => ‖w‖ * y)
      = ProbabilityTheory.gaussianReal 0 ((‖w‖ ^ 2).toNNReal) := by
    rw [hstd, ProbabilityTheory.gaussianReal_map_const_mul, mul_zero, mul_one,
      Real.toNNReal_of_nonneg (sq_nonneg ‖w‖)]
  have hfun : (fun z : E => inner ℝ z w) = ⇑(innerSL ℝ w) := by
    ext z
    rw [coe_innerSL_apply]
    exact (real_inner_comm w z)
  rw [hfun, hL, hR]

end Commons.Probability.Gaussian