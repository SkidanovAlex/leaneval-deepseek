import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

namespace Commons.Analysis.Convolution

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution in
theorem fderiv_fderiv_moll {n : ℕ} (k u : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n))
    (hk : HasCompactSupport k) (hku : ContDiff ℝ (⊤ : ℕ∞) k) (hu : LocallyIntegrable u volume) :
    fderiv ℝ (fderiv ℝ (fun y => ∫ t, u t * k (y - t) ∂volume)) y
      = ∫ t, u t • (fderiv ℝ (fderiv ℝ k) (y - t)) ∂volume := by
  have hk1 : ContDiff ℝ 1 k := hku.of_le (by simp)
  have hk2 : ContDiff ℝ 1 (fderiv ℝ k) := hku.fderiv_right (m := (1 : ℕ)) (by decide)
  have hF_eq : MeasureTheory.convolution (𝕜 := ℝ) u k (ContinuousLinearMap.mul ℝ ℝ) volume
      = fun y => ∫ t, u t * k (y - t) ∂volume := by
    funext z
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
  have hF1 : fderiv ℝ (fun y => ∫ t, u t * k (y - t) ∂volume)
      = fun z => MeasureTheory.convolution (𝕜 := ℝ) u (fderiv ℝ k)
          (ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n))
            (ContinuousLinearMap.mul ℝ ℝ)) volume z := by
    funext z
    have h := hk.hasFDerivAt_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ) hu hk1 z
    rw [hF_eq] at h
    exact h.fderiv
  have hG1 : fderiv ℝ (fun z => MeasureTheory.convolution (𝕜 := ℝ) u (fderiv ℝ k)
        (ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n))
          (ContinuousLinearMap.mul ℝ ℝ)) volume z)
      = fun z => MeasureTheory.convolution (𝕜 := ℝ) u (fderiv ℝ (fderiv ℝ k))
          (ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n))
            (ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n))
              (ContinuousLinearMap.mul ℝ ℝ))) volume z := by
    funext z
    have h := (hk.fderiv ℝ).hasFDerivAt_convolution_right
      (L := ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n))
        (ContinuousLinearMap.mul ℝ ℝ)) hu hk2 z
    exact h.fderiv
  rw [hF1, hG1]
  beta_reduce
  rw [MeasureTheory.convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  ext x
  simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    smul_apply, smul_eq_mul]

end Commons.Analysis.Convolution