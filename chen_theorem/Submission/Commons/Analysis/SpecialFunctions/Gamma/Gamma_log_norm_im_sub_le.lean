import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.hasDerivAt_log_norm_Gamma_vertical
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_im_lower

open Complex Filter
open scoped Real Topology
set_option autoImplicit false
noncomputable section

namespace Commons.Analysis.SpecialFunctions.Gamma

theorem Gamma_log_norm_im_sub_le (u T₀ T' : ℝ) (hu : (1 : ℝ) / 2 ≤ u) (hu2 : u ≤ 8)
    (hT₀ : 1 ≤ T₀) (hT : T₀ ≤ T') :
    Real.log ‖Complex.Gamma ((u : ℂ) + (T' : ℝ) * Complex.I)‖ -
        Real.log ‖Complex.Gamma ((u : ℂ) + (T₀ : ℝ) * Complex.I)‖ ≤
      -(Real.pi / 2) * (T' - T₀) + u * Real.log (T' / T₀) + (1 / 2) * (T' - T₀) := by
  have hu_pos : 0 < u := by linarith
  have hT₀pos : 0 < T₀ := by linarith
  have hT'pos : 0 < T' := lt_of_lt_of_le hT₀pos hT
  set Φ : ℝ → ℝ := fun y => Real.log ‖Complex.Gamma ((u : ℂ) + (y : ℂ) * Complex.I)‖ +
      (Real.pi / 2) * y - u * Real.log y - (1 / 2) * y with hΦ
  have hcont : ContinuousOn Φ (Set.Icc T₀ T') := by
    rw [hΦ]
    intro y hy
    have hypos : 0 < y := by linarith [hy.1, hT₀pos]
    have hFcont : ContinuousAt
        (fun y : ℝ => Real.log ‖Complex.Gamma ((u : ℂ) + (y : ℂ) * Complex.I)‖) y :=
      (hasDerivAt_log_norm_Gamma_vertical u y hu_pos).continuousAt
    have hlogcont : ContinuousAt (fun y : ℝ => u * Real.log y) y :=
      (Real.continuousAt_log (ne_of_gt hypos)).const_mul u
    have hπy : ContinuousAt (fun y : ℝ => (Real.pi / 2) * y) y :=
      continuousAt_const.mul continuousAt_id
    have h12y : ContinuousAt (fun y : ℝ => (1 / 2 : ℝ) * y) y :=
      continuousAt_const.mul continuousAt_id
    exact (((hFcont.add hπy).sub hlogcont).sub h12y).continuousWithinAt
  have hdiffOn : DifferentiableOn ℝ Φ (interior (Set.Icc T₀ T')) := by
    rw [hΦ, interior_Icc]
    intro y hy
    have hypos : 0 < y := by linarith [hy.1, hT₀pos]
    have hFd : HasDerivAt (fun y : ℝ => Real.log ‖Complex.Gamma ((u : ℂ) + (y : ℂ) * Complex.I)‖)
        (-(Complex.digamma ((u : ℂ) + (y : ℂ) * Complex.I)).im) y :=
      hasDerivAt_log_norm_Gamma_vertical u y hu_pos
    have hπy : HasDerivAt (fun y : ℝ => (Real.pi / 2) * y) (Real.pi / 2) y := by
      simpa using (hasDerivAt_id y).const_mul (Real.pi / 2)
    have hlogy : HasDerivAt (fun y : ℝ => u * Real.log y) (u * y⁻¹) y :=
      (Real.hasDerivAt_log (ne_of_gt hypos)).const_mul u
    have h12y : HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * y) (1 / 2) y := by
      simpa using (hasDerivAt_id y).const_mul (1 / 2 : ℝ)
    exact (((hFd.add hπy).sub hlogy).sub h12y).differentiableAt.differentiableWithinAt
  have hderiv : ∀ y ∈ interior (Set.Icc T₀ T'), deriv Φ y ≤ 0 := by
    rw [hΦ, interior_Icc]
    intro y hy
    have hypos : 0 < y := by linarith [hy.1, hT₀pos]
    have hFd : HasDerivAt (fun y : ℝ => Real.log ‖Complex.Gamma ((u : ℂ) + (y : ℂ) * Complex.I)‖)
        (-(Complex.digamma ((u : ℂ) + (y : ℂ) * Complex.I)).im) y :=
      hasDerivAt_log_norm_Gamma_vertical u y hu_pos
    have hπy : HasDerivAt (fun y : ℝ => (Real.pi / 2) * y) (Real.pi / 2) y := by
      simpa using (hasDerivAt_id y).const_mul (Real.pi / 2)
    have hlogy : HasDerivAt (fun y : ℝ => u * Real.log y) (u * y⁻¹) y :=
      (Real.hasDerivAt_log (ne_of_gt hypos)).const_mul u
    have h12y : HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * y) (1 / 2) y := by
      simpa using (hasDerivAt_id y).const_mul (1 / 2 : ℝ)
    have hdeq : deriv (fun y : ℝ => Real.log ‖Complex.Gamma ((u : ℂ) + (y : ℂ) * Complex.I)‖ +
        (Real.pi / 2) * y - u * Real.log y - (1 / 2) * y) y =
        -(Complex.digamma ((u : ℂ) + (y : ℂ) * Complex.I)).im + Real.pi / 2 - u / y - (1 / 2) := by
      rw [show deriv (fun y : ℝ => Real.log ‖Complex.Gamma ((u : ℂ) + (y : ℂ) * Complex.I)‖ +
          (Real.pi / 2) * y - u * Real.log y - (1 / 2) * y) y =
          -(Complex.digamma ((u : ℂ) + (y : ℂ) * Complex.I)).im + Real.pi / 2 - u * y⁻¹ - (1 / 2)
          from (((hFd.add hπy).sub hlogy).sub h12y).deriv]
      ring
    rw [hdeq]
    have hψ := digamma_im_lower u y hu hu2 hypos
    linarith
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc T₀ T') hcont hdiffOn hderiv
  have hle : Φ T' ≤ Φ T₀ := hanti (Set.left_mem_Icc.mpr hT) (Set.right_mem_Icc.mpr hT) hT
  rw [hΦ] at hle
  have hlogdiv : Real.log (T' / T₀) = Real.log T' - Real.log T₀ :=
    Real.log_div (ne_of_gt hT'pos) (ne_of_gt hT₀pos)
  rw [hlogdiv]
  linarith

end Commons.Analysis.SpecialFunctions.Gamma
