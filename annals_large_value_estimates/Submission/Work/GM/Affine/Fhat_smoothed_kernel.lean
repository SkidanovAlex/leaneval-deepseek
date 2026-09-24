import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup
import Submission.Commons.Analysis.Fourier.poisson_summation_scaled

/-!
# The Fourier transform of the smoothing kernel `T · ψ(T·)`

`smoothed ψ T f` is the convolution of `f` with the rescaled kernel `u ↦ T ψ(T u)`; the Fourier
transform of that kernel is what converts the smoothing in GM §9 into the multiplication by
`Fhat ψSmooth (ξ/T)` on the Fourier side.  Here we compute it:

`Fhat (fun x => T * psiSmooth (T * x)) ξ = Fhat psiSmooth (ξ / T)`.

The prefactor `T` exactly cancels the Jacobian `T⁻¹` of the dilation `u ↦ T u`, so the identity is
`T · T⁻¹ = 1`; no numerical factor appears.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- Pulling a complex constant out of the Fourier transform on `ℝ`:
`𝓕 (c · G) = c · 𝓕 G`. -/
lemma fhat_const_mul_cmplx (c : ℂ) (G : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun u : ℝ => c * G u) ξ = c * 𝓕 G ξ := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with u
  simp only [Circle.smul_def]
  ring

/-- Fourier scaling for a dilation of the argument by a positive factor `T`:
`𝓕 (u ↦ ψ (T u)) y = T⁻¹ · Fhat ψ (y / T)`. -/
lemma fhat_comp_mul_ofReal (ψ : ℝ → ℝ) {T : ℝ} (hT : 0 < T) (y : ℝ) :
    𝓕 (fun x : ℝ => ((ψ (T * x) : ℝ) : ℂ)) y = ((T : ℂ))⁻¹ * Fhat ψ (y / T) := by
  have hN : (0 : ℝ) < T⁻¹ := inv_pos.mpr hT
  have h := Commons.Analysis.Fourier.fourier_comp_div (fun u : ℝ => ((ψ u : ℝ) : ℂ)) hN y
  -- `h : 𝓕 (fun x => ψ (x / T⁻¹)) y = (T⁻¹ : ℂ) * 𝓕 ψ (y * T⁻¹)`
  have hx : (fun x : ℝ => ((ψ (x / T⁻¹) : ℝ) : ℂ))
      = fun x : ℝ => ((ψ (T * x) : ℝ) : ℂ) := by
    funext x
    have h1 : x / T⁻¹ = T * x := by rw [div_eq_mul_inv, inv_inv, mul_comm]
    rw [h1]
  rw [hx] at h
  have h2 : ((T⁻¹ : ℝ) : ℂ) = ((T : ℂ))⁻¹ := Complex.ofReal_inv T
  have h3 : y * T⁻¹ = y / T := (div_eq_mul_inv y T).symm
  rw [h2, h3] at h
  simpa only [Fhat] using h

theorem Fhat_smoothed_kernel {T ξ : ℝ} (hT : 0 < T) :
    Fhat (fun x : ℝ => T * psiSmooth (T * x)) ξ = Fhat psiSmooth (ξ / T) := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have h1 : Fhat (fun x : ℝ => T * psiSmooth (T * x)) ξ
      = (T : ℂ) * 𝓕 (fun x : ℝ => ((psiSmooth (T * x) : ℝ) : ℂ)) ξ := by
    change 𝓕 (fun x : ℝ => ((T * psiSmooth (T * x) : ℝ) : ℂ)) ξ
      = (T : ℂ) * 𝓕 (fun x : ℝ => ((psiSmooth (T * x) : ℝ) : ℂ)) ξ
    rw [show (fun x : ℝ => ((T * psiSmooth (T * x) : ℝ) : ℂ))
        = (fun x : ℝ => (T : ℂ) * ((psiSmooth (T * x) : ℝ) : ℂ)) from by
      funext x
      exact Complex.ofReal_mul T (psiSmooth (T * x))]
    exact fhat_const_mul_cmplx (T : ℂ) _ ξ
  rw [h1, fhat_comp_mul_ofReal psiSmooth hT ξ]
  have : (T : ℂ) * (((T : ℂ))⁻¹ * Fhat psiSmooth (ξ / T)) = Fhat psiSmooth (ξ / T) := by
    rw [← mul_assoc, mul_inv_cancel₀ hT0, one_mul]
  exact this

end

end Work.GM.Affine
