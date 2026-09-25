/-
# The `∂`-derivative: basic kernels

This file collects the elementary facts about `Work.Beltrami.dW` (the `∂`-derivative of a
real-differentiable function `ℂ → ℂ`) that are used in the computation of the singular integral
`∫ u, u⁻¹ * dW H u` for a `C¹` function `H` with compact support
(`Work.Beltrami.integral_inv_mul_dW_eq_ball_sub_div_sq`):

* `dW_mul` — `dW` is a derivation;
* `dW_radial` — `dW` of a radial function `u ↦ h(‖u‖²)` is `deriv h (‖u‖²) * star u`;
* `dW_inv` — `dW (u ↦ u⁻¹) u = -(u²)⁻¹` (`u⁻¹` is holomorphic);
* `dW_cutK` — the `∂`-derivative of the cutoff kernel `cutK ε`;
* `star_mul_inv_eq_normSq_mul_inv_sq` — the identity `star u * u⁻¹ = ‖u‖² * (u²)⁻¹`.
-/
import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.dbarW_cauchyT_defs
import Submission.Work.Beltrami.tendsto_cutK_mul
import Submission.Work.Beltrami.integral_radial_weight_inv_sq_eq_zero

noncomputable section

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff RealInnerProductSpace

/-- `dW` is a derivation. -/
theorem dW_mul {F G : ℂ → ℂ} {u : ℂ} (hF : DifferentiableAt ℝ F u)
    (hG : DifferentiableAt ℝ G u) :
    dW (fun y => F y * G y) u = dW F u * G u + F u * dW G u := by
  unfold dW dzCoeff
  rw [fderiv_fun_mul hF hG]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- `dW` of a radial function `u ↦ h(‖u‖²)`. -/
theorem dW_radial {h : ℝ → ℝ} (hh : Differentiable ℝ h) (u : ℂ) :
    dW (fun u : ℂ => (h (‖u‖^2) : ℂ)) u = ((deriv h (‖u‖^2) : ℝ) : ℂ) * star u := by
  have h2 : HasFDerivAt h (ContinuousLinearMap.toSpanSingleton ℝ (deriv h (‖u‖^2))) (‖u‖^2) :=
    (hh (‖u‖^2)).hasDerivAt.hasFDerivAt
  have h1 : HasFDerivAt (fun u : ℂ => ‖u‖^2) (2 • innerSL ℝ u) u := by
    rw [← fderiv_norm_sq_apply u]
    exact ((contDiffAt_id.norm_sq ℝ).differentiableAt one_ne_zero).hasFDerivAt
  have h3 : HasFDerivAt (fun u : ℂ => h (‖u‖^2))
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv h (‖u‖^2))).comp (2 • innerSL ℝ u)) u :=
    h2.comp u h1
  have h4 : HasFDerivAt (fun u : ℂ => (h (‖u‖^2) : ℂ))
      (Complex.ofRealCLM.comp
        ((ContinuousLinearMap.toSpanSingleton ℝ (deriv h (‖u‖^2))).comp (2 • innerSL ℝ u))) u :=
    (Complex.ofRealCLM.hasFDerivAt).comp u h3
  unfold dW dzCoeff
  rw [h4.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_apply, smul_eq_mul, Complex.ofRealCLM_apply, innerSL_apply_apply]
  rw [show inner ℝ u (1:ℂ) = u.re by simp, show inner ℝ u Complex.I = u.im by simp]
  set c : ℝ := deriv h (‖u‖^2) with hc
  rw [Complex.star_def]
  conv_rhs => rw [← Complex.re_add_im u]
  simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- `dW` of `u ↦ u⁻¹` (the holomorphic function `1/u`): `dW (u↦u⁻¹) u = -(u²)⁻¹`. -/
theorem dW_inv {u : ℂ} (hu : u ≠ 0) : dW (fun z : ℂ => z⁻¹) u = -(u ^ 2)⁻¹ := by
  have h1 := (hasDerivAt_inv hu).hasFDerivAt
  have h2 : HasFDerivAt (fun z : ℂ => z⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℂ (-(u ^ 2)⁻¹)).restrictScalars ℝ) u :=
    h1.restrictScalars ℝ
  unfold dW dzCoeff
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  rw [I_mul_I_mul]; ring

/-- The `∂`-derivative of the cutoff kernel `cutK ε u = ψ(‖u‖²/ε² - 1) · u⁻¹`, away from the
origin. -/
theorem dW_cutK (ε : ℝ) {u : ℂ} (hu : u ≠ 0) :
    dW (cutK ε) u = ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ) * (star u * u⁻¹)
      - (cutProfile ε (‖u‖^2) : ℂ) * (u ^ 2)⁻¹ := by
  have hFd : DifferentiableAt ℝ (fun u : ℂ => (cutProfile ε (‖u‖^2) : ℂ)) u := by
    have hd : Differentiable ℝ (fun u : ℂ => cutProfile ε (‖u‖^2)) :=
      (differentiable_cutProfile ε).comp
        ((contDiff_norm_sq (𝕜 := ℝ) (n := 1)).differentiable (by simp))
    exact Complex.ofRealCLM.differentiableAt.comp u hd.differentiableAt
  have hGd : DifferentiableAt ℝ (fun z : ℂ => z⁻¹) u := differentiableAt_id.inv hu
  have hmul := dW_mul (F := fun u : ℂ => (cutProfile ε (‖u‖^2) : ℂ))
    (G := fun z : ℂ => z⁻¹) hFd hGd
  rw [show cutK ε = fun y : ℂ => (cutProfile ε (‖y‖^2) : ℂ) * y⁻¹ from rfl, hmul,
    dW_radial (differentiable_cutProfile ε) u, dW_inv hu]
  ring

/-- The angular factor of the Cauchy kernel is a radial weight times `w⁻²`:
`star u * u⁻¹ = ‖u‖² * (u²)⁻¹`. -/
theorem star_mul_inv_eq_normSq_mul_inv_sq (u : ℂ) :
    star u * u⁻¹ = (‖u‖^2 : ℂ) * (u^2)⁻¹ := by
  rcases eq_or_ne u 0 with h | h
  · subst h; simp
  · field_simp
    rw [mul_comm]
    exact RCLike.mul_conj u

/-- **Integration by parts for the `∂`-operator.**  For real-differentiable `F`, `G` with all the
relevant products integrable, `∫ F * ∂G = -∫ ∂F * G`.  This is the `∂`-analogue of
`Work.Beltrami.integral_mul_dbarW_eq_neg`. -/
theorem integral_mul_dW_eq_neg (F G : ℂ → ℂ)
    (hFG : Integrable (fun u => F u * G u) volume)
    (hF1 : Integrable (fun u => (fderiv ℝ F u 1) * G u) volume)
    (hFI : Integrable (fun u => (fderiv ℝ F u Complex.I) * G u) volume)
    (h1G : Integrable (fun u => F u * (fderiv ℝ G u 1)) volume)
    (hIG : Integrable (fun u => F u * (fderiv ℝ G u Complex.I)) volume)
    (hFd : ∀ u ∈ tsupport G, DifferentiableAt ℝ F u)
    (hGd : ∀ u ∈ tsupport F, DifferentiableAt ℝ G u) :
    ∫ u, F u * dW G u ∂volume = -∫ u, dW F u * G u ∂volume := by
  have h1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := (1:ℂ))
    hF1 h1G hFG hFd hGd
  have hI := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := Complex.I)
    hFI hIG hFG hFd hGd
  have hL : ∫ u, F u * dW G u
      = (2:ℂ)⁻¹ * ((∫ u, F u * (fderiv ℝ G u 1))
          - Complex.I * (∫ u, F u * (fderiv ℝ G u Complex.I))) := by
    rw [show (∫ u, F u * dW G u)
        = ∫ u, (2:ℂ)⁻¹ * (F u * (fderiv ℝ G u 1)
            - Complex.I * (F u * (fderiv ℝ G u Complex.I))) by
        congr 1 with u; rw [dW, dzCoeff]; ring]
    rw [integral_const_mul, integral_sub h1G (hIG.const_mul Complex.I), integral_const_mul]
  have hR : ∫ u, dW F u * G u
      = (2:ℂ)⁻¹ * ((∫ u, (fderiv ℝ F u 1) * G u)
          - Complex.I * (∫ u, (fderiv ℝ F u Complex.I) * G u)) := by
    rw [show (∫ u, dW F u * G u)
        = ∫ u, (2:ℂ)⁻¹ * ((fderiv ℝ F u 1) * G u
            - Complex.I * ((fderiv ℝ F u Complex.I) * G u)) by
        congr 1 with u; rw [dW, dzCoeff]; ring]
    rw [integral_const_mul, integral_sub hF1 (hFI.const_mul Complex.I), integral_const_mul]
  rw [hL, hR, h1, hI]
  ring

end Work.Beltrami
