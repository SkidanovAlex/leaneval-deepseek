import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Submission.Commons.Analysis.Integral.integral_Ioo_inv_sq

namespace Commons.Analysis.Fresnel

open Complex MeasureTheory intervalIntegral

set_option autoImplicit false

/-- Integration-by-parts bound for the tail of the complex Gaussian: for `c` with `0 < c.re`
and `0 < U ≤ T`, `‖∫_U^T exp(-c u²) du‖ ≤ 1/(‖c‖ · U)`. -/
theorem cexp_neg_mul_sq_interval_bound (c : ℂ) (hc : 0 < c.re) {U T : ℝ} (hU : 0 < U)
    (hUT : U ≤ T) :
    ‖∫ u in U..T, Complex.exp (-c * (u : ℂ)^2)‖ ≤ 1 / (‖c‖ * U) := by
  have hTpos : 0 < T := lt_of_lt_of_le hU hUT
  have hcne : c ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
  have hcnormpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
  -- The Gaussian kernel, written with an explicit product so that `*`-based
  -- calculus lemmas apply without instance ambiguity.
  let N : ℝ → ℂ := fun x => Complex.exp (-c * ((x : ℂ) * (x : ℂ)))
  let G : ℝ → ℂ := fun x => N x * (x : ℂ)⁻¹
  let G' : ℝ → ℂ := fun x => (-2 * c) * N x - N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)
  -- Norm bound on the Gaussian kernel.
  have hN_le : ∀ x : ℝ, ‖N x‖ ≤ 1 := by
    intro x
    have hre : (-c * ((x : ℂ) * (x : ℂ))).re = -c.re * x^2 := by
      rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    show ‖Complex.exp (-c * ((x : ℂ) * (x : ℂ)))‖ ≤ 1
    rw [Complex.norm_exp, hre]
    exact Real.exp_le_one_iff.mpr (by nlinarith [hc, sq_nonneg x])
  -- Derivative of the Gaussian kernel.
  have hN_deriv : ∀ x : ℝ, HasDerivAt N (N x * (-c * (2 * (x : ℂ)))) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x :=
      (hasDerivAt_id (x : ℂ)).comp_ofReal
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * (y : ℂ)) (2 * (x : ℂ)) x := by
      have h := h1.mul h1
      rw [show (1 : ℂ) * (x : ℂ) + (x : ℂ) * 1 = 2 * (x : ℂ) by ring] at h
      exact h
    have h3 : HasDerivAt (fun y : ℝ => -c * ((y : ℂ) * (y : ℂ))) (-c * (2 * (x : ℂ))) x :=
      h2.const_mul (-c)
    have h4 : HasDerivAt (fun y : ℝ => Complex.exp (-c * ((y : ℂ) * (y : ℂ))))
        (Complex.exp (-c * ((x : ℂ) * (x : ℂ))) * (-c * (2 * (x : ℂ)))) x := h3.cexp
    exact h4
  -- Derivative of `N x / x`.
  have hG_deriv : ∀ x ∈ Set.Ioo U T, HasDerivAt G (G' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hU (le_of_lt hx.1))
    have hzx : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x :=
      (hasDerivAt_id (x : ℂ)).comp_ofReal
    have hM_deriv : HasDerivAt (fun y : ℝ => (y : ℂ)⁻¹) (-(1 : ℂ) / (x : ℂ)^2) x :=
      h1.inv hzx
    have hprod : HasDerivAt G
        (N x * (-c * (2 * (x : ℂ))) * (x : ℂ)⁻¹ + N x * (-(1 : ℂ) / (x : ℂ)^2)) x :=
      (hN_deriv x).mul hM_deriv
    have hval : N x * (-c * (2 * (x : ℂ))) * (x : ℂ)⁻¹ + N x * (-(1 : ℂ) / (x : ℂ)^2)
        = G' x := by
      have hzz : (x : ℂ) * (x : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hzx
      change N x * (-c * (2 * (x : ℂ))) * (x : ℂ)⁻¹ + N x * (-(1 : ℂ) / (x : ℂ)^2)
        = (-2 * c) * N x - N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)
      rw [show N x * (-c * (2 * (x : ℂ))) * (x : ℂ)⁻¹
            = ((-2 * c) * N x) * ((x : ℂ) * (x : ℂ)⁻¹) by ring, hzz, mul_one]
      rw [show (-(1 : ℂ)) / (x : ℂ)^2 = -((x : ℂ)⁻¹ * (x : ℂ)⁻¹) by
        rw [div_eq_mul_inv, neg_mul, one_mul, pow_two, mul_inv_rev]]
      ring
    rw [hval] at hprod
    exact hprod
  -- Continuity.
  have hN_cont : Continuous N := by
    change Continuous (fun x : ℝ => Complex.exp (-c * ((x : ℂ) * (x : ℂ))))
    fun_prop
  have hinv_cont : ContinuousOn (fun x : ℝ => (x : ℂ)⁻¹) (Set.Icc U T) := by
    refine ContinuousOn.inv₀ Complex.continuous_ofReal.continuousOn ?_
    intro x hx
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hU hx.1))
  have hG_cont : ContinuousOn G (Set.Icc U T) := hN_cont.continuousOn.mul hinv_cont
  have hterm1 : ContinuousOn (fun x : ℝ => (-2 * c) * N x) (Set.Icc U T) :=
    hN_cont.continuousOn.const_mul ((-2 : ℂ) * c)
  have hterm2 : ContinuousOn (fun x : ℝ => N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)) (Set.Icc U T) :=
    hN_cont.continuousOn.mul (hinv_cont.mul hinv_cont)
  have hG'_int : IntervalIntegrable G' volume U T :=
    ContinuousOn.intervalIntegrable_of_Icc hUT (hterm1.sub hterm2)
  have hterm1_int : IntervalIntegrable (fun x : ℝ => (-2 * c) * N x) volume U T :=
    ContinuousOn.intervalIntegrable_of_Icc hUT hterm1
  have hterm2_int : IntervalIntegrable (fun x : ℝ => N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹))
      volume U T :=
    ContinuousOn.intervalIntegrable_of_Icc hUT hterm2
  -- Fundamental theorem of calculus applied to `N x / x`.
  have hFTC : ∫ x in U..T, G' x = G T - G U :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hUT hG_cont hG_deriv hG'_int
  have hsplit : (∫ x in U..T, G' x)
      = (-2 * c) * (∫ x in U..T, N x)
        - (∫ x in U..T, N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)) := by
    change (∫ x in U..T, ((-2 * c) * N x - N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)))
      = (-2 * c) * (∫ x in U..T, N x)
        - (∫ x in U..T, N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹))
    rw [intervalIntegral.integral_sub hterm1_int hterm2_int,
      intervalIntegral.integral_const_mul]
  have hkey : (-2 * c) * (∫ x in U..T, N x)
      - (∫ x in U..T, N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)) = G T - G U := by
    rw [← hsplit]
    exact hFTC
  have hkey2 : (-2 * c) * (∫ x in U..T, N x)
      = (G T - G U) + (∫ x in U..T, N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)) :=
    sub_eq_iff_eq_add.mp hkey
  -- Boundary terms.
  have hGT : ‖G T‖ ≤ 1 / T := by
    have hEq : ‖G T‖ = ‖N T‖ * T⁻¹ := by
      show ‖N T * (T : ℂ)⁻¹‖ = ‖N T‖ * T⁻¹
      rw [norm_mul, norm_inv, Complex.norm_of_nonneg hTpos.le]
    rw [hEq]
    simpa using mul_le_of_le_one_left (inv_nonneg.mpr hTpos.le) (hN_le T)
  have hGU : ‖G U‖ ≤ 1 / U := by
    have hEq : ‖G U‖ = ‖N U‖ * U⁻¹ := by
      show ‖N U * (U : ℂ)⁻¹‖ = ‖N U‖ * U⁻¹
      rw [norm_mul, norm_inv, Complex.norm_of_nonneg hU.le]
    rw [hEq]
    simpa using mul_le_of_le_one_left (inv_nonneg.mpr hU.le) (hN_le U)
  -- The remainder integral.
  have hnorm_inv_sq : ∀ x : ℝ, 0 < x → ‖(x : ℂ)⁻¹ * (x : ℂ)⁻¹‖ = 1 / x^2 := by
    intro x hx
    rw [norm_mul, norm_inv, Complex.norm_of_nonneg hx.le, one_div]
    rw [← pow_two, inv_pow]
  have hR : ‖∫ x in U..T, N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)‖ ≤ 1 / U - 1 / T := by
    have h1 : ‖∫ x in U..T, N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)‖
        ≤ ∫ x in U..T, ‖N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hUT
    have hint1 : IntervalIntegrable (fun x : ℝ => ‖N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)‖)
        volume U T :=
      ContinuousOn.intervalIntegrable_of_Icc hUT hterm2.norm
    have hint2 : IntervalIntegrable (fun x : ℝ => (1 : ℝ) / x^2) volume U T := by
      refine ContinuousOn.intervalIntegrable_of_Icc hUT ?_
      refine (continuousOn_const (c := (1 : ℝ))).div (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hU hx.1))
    have h2 : (∫ x in U..T, ‖N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)‖)
        ≤ ∫ x in U..T, (1 : ℝ) / x^2 := by
      refine intervalIntegral.integral_mono_on hUT hint1 hint2 ?_
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hU hx.1
      calc ‖N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)‖
            = ‖N x‖ * ‖(x : ℂ)⁻¹ * (x : ℂ)⁻¹‖ := norm_mul _ _
        _ ≤ 1 * ‖(x : ℂ)⁻¹ * (x : ℂ)⁻¹‖ :=
              mul_le_mul_of_nonneg_right (hN_le x) (norm_nonneg _)
        _ = 1 / x^2 := by rw [one_mul, hnorm_inv_sq x hxpos]
    have h3 : (∫ x in U..T, (1 : ℝ) / x^2) = 1 / U - 1 / T := by
      have hfun : (fun x : ℝ => (1 : ℝ) / x^2) = fun x : ℝ => x⁻¹ * x⁻¹ := by
        funext x
        rw [one_div, ← pow_two, inv_pow]
      rw [hfun, intervalIntegral.integral_of_le hUT,
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
      have hfun' : (fun x : ℝ => x⁻¹ * x⁻¹) = fun x : ℝ => (x⁻¹)^2 := by
        funext x
        rw [pow_two]
      rw [hfun']
      exact Commons.Analysis.Integral.integral_Ioo_inv_sq hU hUT
    linarith
  -- Norm inequality.
  have hmain : ‖(-2 * c) * (∫ x in U..T, N x)‖
      ≤ ‖G T - G U‖ + ‖∫ x in U..T, N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)‖ := by
    rw [hkey2]
    exact norm_add_le _ _
  have hGTU : ‖G T - G U‖ ≤ 1 / T + 1 / U :=
    le_trans (norm_sub_le _ _) (add_le_add hGT hGU)
  have hLHS : ‖(-2 * c) * (∫ x in U..T, N x)‖ = 2 * ‖c‖ * ‖∫ x in U..T, N x‖ := by
    rw [norm_mul]
    rw [show ‖(-2 : ℂ) * c‖ = 2 * ‖c‖ by
      rw [show (-2 : ℂ) * c = -(2 * c) by ring, norm_neg, norm_mul]
      norm_num]
  have hbound : 2 * ‖c‖ * ‖∫ x in U..T, N x‖ ≤ 2 / U := by
    calc 2 * ‖c‖ * ‖∫ x in U..T, N x‖
        = ‖(-2 * c) * (∫ x in U..T, N x)‖ := hLHS.symm
      _ ≤ ‖G T - G U‖ + ‖∫ x in U..T, N x * ((x : ℂ)⁻¹ * (x : ℂ)⁻¹)‖ := hmain
      _ ≤ (1 / T + 1 / U) + (1 / U - 1 / T) := add_le_add hGTU hR
      _ = 2 / U := by ring
  have hpos2c : (0 : ℝ) < 2 * ‖c‖ := by positivity
  have hfinal : ‖∫ x in U..T, N x‖ ≤ 1 / (‖c‖ * U) := by
    have hb' : ‖∫ x in U..T, N x‖ * (2 * ‖c‖) ≤ 2 / U := by
      have h := hbound
      rwa [mul_comm (2 * ‖c‖) (‖∫ x in U..T, N x‖)] at h
    have h1 := (le_div_iff₀ hpos2c).mpr hb'
    have h2 : (2 / U) / (2 * ‖c‖) = 1 / (‖c‖ * U) := by
      field_simp
    rwa [h2] at h1
  -- Translate back to the stated integrand `Complex.exp (-c * (u : ℂ)^2)`.
  have hcongr : (∫ u in U..T, Complex.exp (-c * (u : ℂ)^2)) = ∫ x in U..T, N x := by
    apply intervalIntegral.integral_congr
    intro u _
    show Complex.exp (-c * (u : ℂ)^2) = Complex.exp (-c * ((u : ℂ) * (u : ℂ)))
    rw [pow_two]
  rw [hcongr]
  exact hfinal

end Commons.Analysis.Fresnel