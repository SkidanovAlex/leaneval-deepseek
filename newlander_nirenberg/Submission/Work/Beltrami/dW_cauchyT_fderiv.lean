import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.cauchyInt_fderiv_apply

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff

/-- `dzCoeff` is complex-linear: multiplying a real-linear map by a complex
constant multiplies its `∂`-coefficient by the same constant. -/
lemma dzCoeff_smul (c : ℂ) (L : ℂ →L[ℝ] ℂ) : dzCoeff (c • L) = c * dzCoeff L := by
  unfold dzCoeff
  simp only [smul_apply, smul_eq_mul]
  ring

/-- The `∂`-derivative of the Cauchy transform: for smooth compactly supported `f : ℂ → ℂ` and every `z`, `dW (cauchyT f) z = -(1/π) • ∫ u, u⁻¹ * dW f (z + u)`. Suggested route: `cauchyT f z = ((-(Real.pi)⁻¹ : ℝ) : ℂ) * cauchyInt f z` (`Work.Beltrami.cauchyT_eq_cauchyInt` in `Submission/Work/Beltrami/dbarW_cauchyT.lean`), `dW` commutes with multiplication by a real constant, and `Work.Beltrami.cauchyInt_fderiv_apply` together with `ContinuousLinearMap.integral_apply` gives `dW (cauchyInt f) z = ∫ u, u⁻¹ * dW f (z+u)`; integrability of `u ↦ u⁻¹ • fderiv ℝ f (z+u)` is `Work.Beltrami.integrable_smul_fderiv_cauchyInt`. -/
theorem dW_cauchyT_fderiv (f : ℂ → ℂ) (hf : ContDiff ℝ ⊤ f) (hc : HasCompactSupport f) (z : ℂ) :
    dW (cauchyT f) z = (-(Real.pi)⁻¹) • ∫ u, u⁻¹ * dW f (z + u) ∂volume := by
  set c : ℂ := ((-(Real.pi : ℝ)⁻¹ : ℝ) : ℂ) with hc_def
  -- the integral form of the derivative of the Cauchy integral
  have hInt := integrable_smul_fderiv_cauchyInt f hf hc z
  set L : ℂ →L[ℝ] ℂ := ∫ u, (u⁻¹ : ℂ) • fderiv ℝ f (z + u) ∂volume with hL_def
  have hL : HasFDerivAt (cauchyInt f) L z := by
    rw [hL_def]; exact hasFDerivAt_cauchyInt f hf hc z
  have hfL : fderiv ℝ (cauchyInt f) z = L := hL.fderiv
  have hL1 : L 1 = ∫ u, u⁻¹ * (fderiv ℝ f (z + u) 1) ∂volume := by
    rw [hL_def, ContinuousLinearMap.integral_apply hInt 1]
    apply integral_congr_ae; filter_upwards with u; simp [smul_eq_mul]
  have hLI : L Complex.I = ∫ u, u⁻¹ * (fderiv ℝ f (z + u) Complex.I) ∂volume := by
    rw [hL_def, ContinuousLinearMap.integral_apply hInt Complex.I]
    apply integral_congr_ae; filter_upwards with u; simp [smul_eq_mul]
  -- integrability of the two scalar integrands
  have hg1 : Integrable (fun u => u⁻¹ * (fderiv ℝ f (z + u) 1)) volume := by
    have hcont : Continuous (fun u : ℂ => (fderiv ℝ f (z + u)) 1) :=
      ((hf.continuous_fderiv (by simp)).comp (continuous_const.add continuous_id)).clm_apply
        continuous_const
    have hcs : HasCompactSupport (fun u : ℂ => (fderiv ℝ f (z + u)) 1) :=
      ((hc.fderiv ℝ).comp_homeomorph (Homeomorph.addLeft z)).comp_left
        (g := fun L : ℂ →L[ℝ] ℂ => L 1) (by simp)
    exact (integrable_mul_inv (fun u : ℂ => (fderiv ℝ f (z + u)) 1) hcont hcs).congr
      (Filter.Eventually.of_forall (fun u => by ring))
  have hgI : Integrable (fun u => u⁻¹ * (fderiv ℝ f (z + u) Complex.I)) volume := by
    have hcont : Continuous (fun u : ℂ => (fderiv ℝ f (z + u)) Complex.I) :=
      ((hf.continuous_fderiv (by simp)).comp (continuous_const.add continuous_id)).clm_apply
        continuous_const
    have hcs : HasCompactSupport (fun u : ℂ => (fderiv ℝ f (z + u)) Complex.I) :=
      ((hc.fderiv ℝ).comp_homeomorph (Homeomorph.addLeft z)).comp_left
        (g := fun L : ℂ →L[ℝ] ℂ => L Complex.I) (by simp)
    exact (integrable_mul_inv (fun u : ℂ => (fderiv ℝ f (z + u)) Complex.I) hcont hcs).congr
      (Filter.Eventually.of_forall (fun u => by ring))
  -- rewrite the scalar integrand of `dW f` in coordinates
  have hdWf : (fun u : ℂ => u⁻¹ * dW f (z + u))
      = fun u => (2:ℂ)⁻¹ * (u⁻¹ * (fderiv ℝ f (z + u) 1)
          - Complex.I * (u⁻¹ * (fderiv ℝ f (z + u) Complex.I))) := by
    funext u; rw [dW, dzCoeff]; ring
  have h2 : (∫ u, u⁻¹ * dW f (z + u) ∂volume)
      = (2:ℂ)⁻¹ * ((∫ u, u⁻¹ * (fderiv ℝ f (z + u) 1))
          - Complex.I * (∫ u, u⁻¹ * (fderiv ℝ f (z + u) Complex.I))) := by
    rw [hdWf, integral_const_mul, integral_sub hg1 (hgI.const_mul Complex.I), integral_const_mul]
  -- the derivative of the Cauchy integral has the stated `∂`-coefficient
  have hdW_int : dW (cauchyInt f) z = ∫ u, u⁻¹ * dW f (z + u) ∂volume := by
    have h1 : dW (cauchyInt f) z = (L 1 - Complex.I * L Complex.I) / 2 := by
      unfold dW dzCoeff; rw [hfL]
    rw [h1, hL1, hLI, h2]
    ring
  -- `cauchyT` is a real multiple of `cauchyInt`, so its `∂`-derivative scales
  have hcT : cauchyT f = fun y => c * cauchyInt f y := by
    funext y; rw [hc_def]; exact cauchyT_eq_cauchyInt f y
  have hderiv : fderiv ℝ (cauchyT f) z = c • L := by
    rw [hcT]; exact (hL.const_mul c).fderiv
  have hdz : dW (cauchyT f) z = c * ∫ u, u⁻¹ * dW f (z + u) ∂volume := by
    rw [dW, hderiv, dzCoeff_smul]
    have : dzCoeff L = ∫ u, u⁻¹ * dW f (z + u) ∂volume := by
      rw [← hfL]; exact hdW_int
    rw [this]
  rw [hdz, hc_def, Complex.real_smul]

end Work.Beltrami
