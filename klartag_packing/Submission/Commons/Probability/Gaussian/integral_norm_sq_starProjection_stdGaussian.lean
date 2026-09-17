import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace Commons.Probability.Gaussian

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

noncomputable section

/-- The second moment of a linear functional under the standard Gaussian on a finite-dimensional
real inner product space equals the squared norm of the representing vector. -/
lemma integral_inner_sq_stdGaussian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (x : E) :
    ∫ z, (⟪x, z⟫_ℝ) ^ 2 ∂(ProbabilityTheory.stdGaussian E) = ‖x‖ ^ 2 := by
  have hmean : ∫ z : E, id z ∂(ProbabilityTheory.stdGaussian E) = 0 := by
    simp [integral_id_stdGaussian]
  have h := covarianceBilin_apply (μ := ProbabilityTheory.stdGaussian E)
    (IsGaussian.memLp_two_id) x x
  simp only [hmean, sub_zero, covarianceBilin_stdGaussian] at h
  rw [innerSL_apply_apply ℝ x x, real_inner_self_eq_norm_sq] at h
  simpa only [pow_two] using h.symm

theorem integral_norm_sq_starProjection_stdGaussian {d : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    ∫ x, ‖V.starProjection x‖ ^ 2 ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))
      = (Module.finrank ℝ V : ℝ) := by
  set b := stdOrthonormalBasis ℝ V with hb
  have hkey : ∀ z : EuclideanSpace ℝ (Fin d),
      ‖V.starProjection z‖ ^ 2 = ∑ i, (⟪(b i : EuclideanSpace ℝ (Fin d)), z⟫_ℝ) ^ 2 := by
    intro z
    have h := b.sum_sq_inner_right ⟨V.starProjection z, V.starProjection_apply_mem z⟩
    rw [Submodule.coe_norm] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_inner,
      ← Submodule.inner_starProjection_left_eq_right V (b i : EuclideanSpace ℝ (Fin d)) z,
      Submodule.starProjection_mem_subspace_eq_self (b i)]
  calc ∫ x, ‖V.starProjection x‖ ^ 2
        ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))
      = ∫ x, ∑ i, (⟪(b i : EuclideanSpace ℝ (Fin d)), x⟫_ℝ) ^ 2
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        simp only [hkey]
    _ = ∑ i, ∫ x, (⟪(b i : EuclideanSpace ℝ (Fin d)), x⟫_ℝ) ^ 2
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [integral_finsetSum]
        intro i _
        simpa [innerSL_apply_apply] using
          ((innerSL ℝ (b i : EuclideanSpace ℝ (Fin d))).comp_memLp'
            IsGaussian.memLp_two_id).integrable_sq
    _ = ∑ i, ‖(b i : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact integral_inner_sq_stdGaussian _
    _ = ∑ _i : Fin (Module.finrank ℝ V), (1 : ℝ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Submodule.coe_norm (b i), OrthonormalBasis.norm_eq_one b i]
        norm_num
    _ = (Module.finrank ℝ V : ℝ) := by simp

end

end Commons.Probability.Gaussian