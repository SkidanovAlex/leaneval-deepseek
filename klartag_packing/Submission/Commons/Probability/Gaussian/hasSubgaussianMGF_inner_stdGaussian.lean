import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.SubGaussian

namespace Commons.Probability.Gaussian

open MeasureTheory ProbabilityTheory
open scoped Real

theorem hasSubgaussianMGF_inner_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (v : E) :
    ProbabilityTheory.HasSubgaussianMGF (fun x : E => inner ℝ x v) (‖v‖₊ ^ 2)
      (ProbabilityTheory.stdGaussian E) := by
  have hinner : (fun x : E => inner ℝ x v) = fun x => innerSL ℝ v x := by
    funext x
    rw [real_inner_comm]
    rfl
  have hmap : (stdGaussian E).map (fun x : E => inner ℝ x v) = gaussianReal 0 (‖v‖₊ ^ 2) := by
    rw [hinner, IsGaussian.map_eq_gaussianReal]
    congr 1
    · rw [integral_strongDual_stdGaussian]
    · rw [variance_dual_stdGaussian, innerSL_apply_norm, Real.toNNReal_pow (norm_nonneg v) 2]
      simp
  have hg : HasSubgaussianMGF id (‖v‖₊ ^ 2) (gaussianReal 0 (‖v‖₊ ^ 2)) := by
    constructor
    · intro t
      simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := ‖v‖₊ ^ 2) t
    · intro t
      rw [mgf_id_gaussianReal]
      simp
  exact (HasSubgaussianMGF.id_map_iff (by fun_prop : AEMeasurable (fun x : E => inner ℝ x v) (stdGaussian E))).1 (hmap.symm ▸ hg)

end Commons.Probability.Gaussian