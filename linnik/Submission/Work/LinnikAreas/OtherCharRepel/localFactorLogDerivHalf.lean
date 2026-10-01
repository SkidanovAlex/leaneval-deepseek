import Mathlib

namespace Work.LinnikAreas.OtherCharRepel

/-- For a complex number `w` with `‖w‖ < 1`, the real part of `w / (1 - w)` is at least `-1/2`.

This is sharp: for `‖w‖ = 1`, `w ≠ 1` the value is exactly `-1/2`. -/
private lemma neg_half_le_re_div_one_sub (w : ℂ) (hw : ‖w‖ < 1) :
    -(1 / 2 : ℝ) ≤ (w / (1 - w)).re := by
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have hw1 : w = 1 := by
      have h2 : w = 1 - (1 - w) := by ring
      rw [h, sub_zero] at h2
      exact h2
    rw [hw1, norm_one] at hw
    exact absurd hw (lt_irrefl 1)
  have hNpos : 0 < Complex.normSq ((1 : ℂ) - w) := Complex.normSq_pos.mpr hne
  have hNle : w.re * w.re + w.im * w.im ≤ 1 := by
    have h : Complex.normSq w ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [hw, norm_nonneg w]
    rwa [Complex.normSq_apply] at h
  have hident : w / (1 - w) = ((1 - w)⁻¹) - 1 := by field_simp; ring
  have hkey : Complex.normSq ((1 : ℂ) - w) ≤ 2 * ((1 : ℂ) - w).re := by
    have h1 : Complex.normSq ((1 : ℂ) - w) =
        (1 - w.re) * (1 - w.re) + (-w.im) * (-w.im) := by
      rw [Complex.normSq_apply]; simp [Complex.sub_re, Complex.sub_im]
    have h3 : ((1 : ℂ) - w).re = 1 - w.re := by simp [Complex.sub_re]
    rw [h1, h3]
    nlinarith [hNle]
  rw [hident, Complex.sub_re, Complex.one_re, Complex.inv_re]
  have hfac : (1 / 2 : ℝ) ≤ ((1 : ℂ) - w).re / Complex.normSq ((1 : ℂ) - w) := by
    rw [le_div_iff₀ hNpos]
    nlinarith [hkey]
  linarith

/-- At a complex point `z` with `1 < Re z`, the real part of the logarithmic derivative of the
local Euler factor `1 - c * p ^ (-s)` is at least `-(1/2) * log p`, for any `c` of modulus at
most `1` and any prime `p`. -/
theorem localFactorLogDerivHalf (p : ℕ) (hp : p.Prime) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (z : ℂ) (hz : 1 < z.re) :
    -(1 / 2) * Real.log (p : ℝ) ≤
      (logDeriv (fun w : ℂ => 1 - c * (p : ℂ) ^ (-w)) z).re := by
  have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpgt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  -- the logarithmic derivative equals `log p * (w / (1 - w))` with `w = c * p ^ (-z)`
  have hld : logDeriv (fun w : ℂ => 1 - c * (p : ℂ) ^ (-w)) z
      = (Real.log p : ℂ) *
          (c * (p : ℂ) ^ (-z) / (1 - c * (p : ℂ) ^ (-z))) := by
    have hlog_eq : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
      rw [← Complex.ofReal_natCast p, ← Complex.ofReal_log (le_of_lt hppos)]
    have hbase : (fun w : ℂ => (p : ℂ) ^ (-w)) =
        (fun y : ℂ => (p : ℂ) ^ y) ∘ (fun w : ℂ => -w) := rfl
    have h1 : HasDerivAt (fun y : ℂ => (p : ℂ) ^ y)
        ((p : ℂ) ^ (-z) * Complex.log (p : ℂ)) (-z) :=
      (Complex.hasStrictDerivAt_const_cpow (x := (p : ℂ)) (y := -z)
        (Or.inl hpne)).hasDerivAt
    have h2 : HasDerivAt (fun w : ℂ => -w) (-1) z := hasDerivAt_neg z
    have h3 : HasDerivAt (fun w : ℂ => (p : ℂ) ^ (-w))
        (((p : ℂ) ^ (-z) * Complex.log (p : ℂ)) * (-1)) z := by
      rw [hbase]; exact h1.comp z h2
    have h5 : HasDerivAt (fun w : ℂ => 1 - c * (p : ℂ) ^ (-w))
        (0 - c * (((p : ℂ) ^ (-z) * Complex.log (p : ℂ)) * (-1))) z :=
      (hasDerivAt_const z (1 : ℂ)).sub (h3.const_mul c)
    have hderiv : deriv (fun w : ℂ => 1 - c * (p : ℂ) ^ (-w)) z
        = c * (p : ℂ) ^ (-z) * (Real.log p : ℂ) := by
      rw [h5.deriv, hlog_eq]; ring
    rw [logDeriv]
    simp only [Pi.div_apply]
    rw [hderiv]
    ring
  rw [hld]
  set w : ℂ := c * (p : ℂ) ^ (-z) with hw
  -- the modulus of `w` is `< 1` because `Re z > 1`
  have hwnorm : ‖w‖ < 1 := by
    have hvn : ‖(p : ℂ) ^ (-z)‖ = (p : ℝ) ^ (-z.re) := by
      rw [← Complex.ofReal_natCast p, Complex.norm_cpow_eq_rpow_re_of_pos hppos]
      simp only [Complex.neg_re]
    have hlt : (p : ℝ) ^ (-z.re) < 1 := by
      rw [Real.rpow_neg (le_of_lt hppos)]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hpgt1 (by linarith))
    calc ‖w‖ = ‖c‖ * ‖(p : ℂ) ^ (-z)‖ := by rw [hw, norm_mul]
      _ ≤ 1 * (p : ℝ) ^ (-z.re) := by
            rw [hvn]
            exact mul_le_mul_of_nonneg_right hc (le_of_lt (Real.rpow_pos_of_pos hppos _))
      _ = (p : ℝ) ^ (-z.re) := one_mul _
      _ < 1 := hlt
  have hbound : -(1 / 2 : ℝ) ≤ (w / (1 - w)).re := neg_half_le_re_div_one_sub w hwnorm
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h2 := mul_le_mul_of_nonneg_left hbound hlogp
  linarith

end Work.LinnikAreas.OtherCharRepel
