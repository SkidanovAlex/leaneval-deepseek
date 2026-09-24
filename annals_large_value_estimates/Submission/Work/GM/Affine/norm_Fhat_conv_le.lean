import Mathlib
import Submission.Work.GM.Affine.setup

/-!
# The Fourier transform of `φ ⋆ f` is bounded by that of `f`

For a nonnegative continuous compactly supported `φ : ℝ → ℝ` with `∫ φ = 1` (an *approximate
identity*), convolving `f` with `φ` does not increase the (complex) Fourier transform:

  `‖Fhat (φ ⋆ f) ξ‖ ≤ ‖Fhat f ξ‖`.

The mathematics is the convolution theorem
`Fhat (φ ⋆ f) ξ = Fhat φ ξ * Fhat f ξ` together with the trivial bound
`‖Fhat φ ξ‖ = ‖∫ e(-u ξ) φ u‖ ≤ ∫ φ = 1`.
-/

open MeasureTheory
open scoped FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- `‖Fhat φ ξ‖ ≤ ∫ φ` for a nonnegative `φ`. -/
lemma norm_Fhat_le_integral {φ : ℝ → ℝ} (hφnn : ∀ x, 0 ≤ φ x) (ξ : ℝ) :
    ‖Fhat φ ξ‖ ≤ ∫ x, φ x := by
  rw [Fhat, Real.fourier_eq]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  rw [Circle.norm_smul]
  rw [show ‖(φ u : ℂ)‖ = ‖φ u‖ from by simp, Real.norm_of_nonneg (hφnn u)]

/-- `‖Fhat φ ξ‖ ≤ 1` for a nonnegative `φ` with `∫ φ = 1`. -/
lemma norm_Fhat_le_one {φ : ℝ → ℝ} (hφnn : ∀ x, 0 ≤ φ x) (hφ1 : ∫ x, φ x = 1) (ξ : ℝ) :
    ‖Fhat φ ξ‖ ≤ 1 := by
  rw [← hφ1]
  exact norm_Fhat_le_integral hφnn ξ

/-- `Fhat (φ ⋆ f) ξ = Fhat φ ξ * Fhat f ξ` for continuous compactly supported `φ` and integrable
`f`: the convolution theorem. -/
lemma Fhat_convolution_eq {φ f : ℝ → ℝ} (hφc : Continuous φ) (hφcs : HasCompactSupport φ)
    (hfi : MeasureTheory.Integrable f) (ξ : ℝ) :
    Fhat (MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) ξ
      = Fhat φ ξ * Fhat f ξ := by
  have hφint : Integrable φ := hφc.integrable_of_hasCompactSupport hφcs
  have hΦint : Integrable (fun u : ℝ => (φ u : ℂ)) := hφint.ofReal
  have hFint : Integrable (fun u : ℝ => (f u : ℂ)) := hfi.ofReal
  -- the real convolution, read in `ℂ`, is the complex convolution
  have hfun : (fun x : ℝ =>
        ((MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) x : ℂ))
      = MeasureTheory.convolution (fun u : ℝ => (φ u : ℂ)) (fun u : ℝ => (f u : ℂ))
          (ContinuousLinearMap.lsmul ℂ ℂ) MeasureTheory.volume := by
    funext x
    rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    simp only [← Complex.ofReal_mul]
    exact (integral_ofReal (f := fun t : ℝ => φ t * f (x - t))).symm
  have h1 : Fhat (MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) ξ
      = FourierTransform.fourier
          (MeasureTheory.convolution (fun u : ℝ => (φ u : ℂ)) (fun u : ℝ => (f u : ℂ))
            (ContinuousLinearMap.lsmul ℂ ℂ) MeasureTheory.volume) ξ := by
    rw [Fhat, hfun]
  rw [h1, Real.fourier_smul_convolution_eq hΦint hFint ξ, Fhat, Fhat, smul_eq_mul]

theorem norm_Fhat_conv_le {φ f : ℝ → ℝ} (hφnn : ∀ x, 0 ≤ φ x) (hφc : Continuous φ)
    (hφcs : HasCompactSupport φ) (hφ1 : ∫ x, φ x = 1)
    (hfc : Continuous f) (hfi : MeasureTheory.Integrable f) :
    ∀ ξ : ℝ,
      ‖Work.GM.Affine.Fhat
        (MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) ξ‖
        ≤ ‖Work.GM.Affine.Fhat f ξ‖ := by
  intro ξ
  rw [Fhat_convolution_eq hφc hφcs hfi ξ, norm_mul]
  calc ‖Fhat φ ξ‖ * ‖Fhat f ξ‖ ≤ 1 * ‖Fhat f ξ‖ :=
        mul_le_mul_of_nonneg_right (norm_Fhat_le_one hφnn hφ1 ξ) (norm_nonneg _)
    _ = ‖Fhat f ξ‖ := one_mul _

end

end Work.GM.Affine
