import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform

namespace Commons.Analysis.Fourier

open MeasureTheory FourierTransform
open scoped Real

theorem fourier_comp_smul {d : ℕ} (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) {c : ℝ}
    (hc : 0 < c) :
    FourierTransform.fourier (fun x : EuclideanSpace ℝ (Fin d) => ψ (c • x)) =
      fun ξ : EuclideanSpace ℝ (Fin d) =>
        (((c ^ d)⁻¹ : ℝ) : ℂ) •
          FourierTransform.fourier (fun x : EuclideanSpace ℝ (Fin d) => ψ x) (c⁻¹ • ξ) := by
  funext ξ
  have hcne : c ≠ 0 := ne_of_gt hc
  rw [Real.fourier_eq, Real.fourier_eq]
  set F : EuclideanSpace ℝ (Fin d) → ℂ :=
    fun y => 𝐞 (-inner ℝ (c⁻¹ • y) ξ) • (ψ y : ℂ) with hF
  have hcomp : (fun v : EuclideanSpace ℝ (Fin d) => 𝐞 (-inner ℝ v ξ) • (ψ (c • v) : ℂ))
      = fun v => F (c • v) := by
    funext v
    simp only [hF]
    rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
  have hFint : ∫ x, F x = ∫ v, 𝐞 (-inner ℝ v (c⁻¹ • ξ)) • (ψ v : ℂ) := by
    apply integral_congr_ae
    filter_upwards with y
    simp only [hF]
    rw [real_inner_smul_left, real_inner_smul_right]
  calc ∫ v, 𝐞 (-inner ℝ v ξ) • (ψ (c • v) : ℂ)
      = ∫ v, F (c • v) := by rw [hcomp]
    _ = |(c ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))⁻¹| • ∫ x, F x :=
          Measure.integral_comp_smul volume F c
    _ = (c ^ d)⁻¹ • ∫ x, F x := by
          rw [finrank_euclideanSpace_fin,
            abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hc.le d))]
    _ = (c ^ d)⁻¹ • ∫ v, 𝐞 (-inner ℝ v (c⁻¹ • ξ)) • (ψ v : ℂ) := by rw [hFint]
    _ = (((c ^ d)⁻¹ : ℝ) : ℂ) • ∫ v, 𝐞 (-inner ℝ v (c⁻¹ • ξ)) • (ψ v : ℂ) := by
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
          rfl

end Commons.Analysis.Fourier