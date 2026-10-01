import Mathlib

namespace Work.LinnikAreas.OtherCharRepel

/-- At a real point `σ > 1`, the real part of the logarithmic derivative of the local Euler
factor `1 - c * p ^ (-s)` is at least `-log p`, for any `c` of modulus at most `1` and any
prime `p`. -/
theorem localFactorReLower (p : ℕ) (hp : p.Prime) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (σ : ℝ) (hσ : 1 < σ) :
    -(Real.log p) ≤
      (logDeriv (fun z : ℂ => 1 - c * (p : ℂ) ^ (-z)) (σ : ℂ)).re := by
  have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hlogp_nn : 0 ≤ Real.log p := Real.log_nonneg hp1
  -- the value `w = c * p ^ (-σ)`, of modulus at most `1`
  set w : ℂ := c * (p : ℂ) ^ (-(σ : ℂ)) with hw
  have hwnorm : ‖w‖ ≤ 1 := by
    rw [hw, norm_mul]
    have hPnorm : ‖(p : ℂ) ^ (-(σ : ℂ))‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast p,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp.pos)]
      simp only [Complex.neg_re, Complex.ofReal_re]
      calc (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (0 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le hp1
            linarith
        _ = 1 := Real.rpow_zero _
    calc ‖c‖ * ‖(p : ℂ) ^ (-(σ : ℂ))‖ ≤ 1 * ‖(p : ℂ) ^ (-(σ : ℂ))‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ = ‖(p : ℂ) ^ (-(σ : ℂ))‖ := one_mul _
      _ ≤ 1 := hPnorm
  -- the logarithmic derivative equals `w * log p / (1 - w)`
  have hderiv : deriv (fun z : ℂ => 1 - c * (p : ℂ) ^ (-z)) (σ : ℂ) = w * (Real.log p : ℂ) := by
    have hlog_eq : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
      rw [← Complex.ofReal_natCast p, ← Complex.ofReal_log (show (0 : ℝ) ≤ (p : ℝ) by positivity)]
    have hbase : (fun z : ℂ => (p : ℂ) ^ (-z)) =
        (fun y : ℂ => (p : ℂ) ^ y) ∘ (fun z : ℂ => -z) := rfl
    have h1 : HasDerivAt (fun y : ℂ => (p : ℂ) ^ y)
        ((p : ℂ) ^ (-(σ : ℂ)) * Complex.log (p : ℂ)) (-(σ : ℂ)) :=
      (Complex.hasStrictDerivAt_const_cpow (x := (p : ℂ)) (y := -(σ : ℂ)) (Or.inl hpne)).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => -z) (-1) (σ : ℂ) := hasDerivAt_neg (σ : ℂ)
    have h3 : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z))
        (((p : ℂ) ^ (-(σ : ℂ)) * Complex.log (p : ℂ)) * (-1)) (σ : ℂ) := by
      rw [hbase]; exact h1.comp (σ : ℂ) h2
    have h5 := (h3.const_mul c).const_sub (1 : ℂ)
    rw [h5.deriv, hlog_eq, hw]
    ring
  have hld : logDeriv (fun z : ℂ => 1 - c * (p : ℂ) ^ (-z)) (σ : ℂ)
      = w * (Real.log p : ℂ) / (1 - w) := by
    rw [logDeriv]
    simp only [Pi.div_apply]
    rw [hderiv, hw]
  rw [hld]
  have key : w * (Real.log p : ℂ) / (1 - w) = (Real.log p : ℂ) * (w / (1 - w)) := by ring
  rw [key, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  simp only [zero_mul, sub_zero]
  -- for `‖w‖ ≤ 1`, `Re (w / (1 - w)) ≥ -1`
  have hwre : -1 ≤ (w / (1 - w)).re := by
    by_cases h : (1 : ℂ) - w = 0
    · rw [h, div_zero, Complex.zero_re]; norm_num
    · have hwle : w.re ≤ 1 := (Complex.re_le_norm w).trans hwnorm
      have h1 : w / (1 - w) = (1 - w)⁻¹ - 1 := by field_simp; ring
      rw [h1, Complex.sub_re, Complex.one_re, Complex.inv_re]
      have hnum : 0 ≤ (1 - w).re := by simp [Complex.sub_re]; linarith
      have hden : 0 ≤ Complex.normSq (1 - w) := Complex.normSq_nonneg _
      have hnonneg : 0 ≤ (1 - w).re / Complex.normSq (1 - w) := div_nonneg hnum hden
      linarith
  have h2 := mul_le_mul_of_nonneg_left hwre hlogp_nn
  rw [mul_neg, mul_one] at h2
  linarith

end Work.LinnikAreas.OtherCharRepel
