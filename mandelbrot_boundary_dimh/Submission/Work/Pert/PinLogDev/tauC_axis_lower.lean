import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert.PinLogDev

open Complex

/-- For `x ≥ 0` one has `x/(1+x) ≤ 1 - e^{-x}` (from `e^x ≥ 1 + x`). -/
lemma div_one_add_le_one_sub_exp_neg (x : ℝ) (hx : 0 ≤ x) :
    x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have h1 : 0 < 1 + x := by linarith
  have hexp : 1 + x ≤ Real.exp x := by have := Real.add_one_le_exp x; linarith
  have hinv : (Real.exp x)⁻¹ ≤ (1 + x)⁻¹ := inv_anti₀ h1 hexp
  have h2 : (1 : ℝ) - (1 + x)⁻¹ = x / (1 + x) := by
    field_simp
    ring
  rw [Real.exp_neg, ← h2]
  linarith

/-- For `z` with `0 ≤ z.re` the reverse triangle inequality gives
`z.re/(1 + z.re) ≤ ‖1 - e^{-z}‖`. -/
lemma le_norm_one_sub_exp_neg_mul (z : ℂ) (hz : 0 ≤ z.re) :
    z.re / (1 + z.re) ≤ ‖1 - Complex.exp (-z)‖ := by
  have hb : |‖(1 : ℂ)‖ - ‖Complex.exp (-z)‖| ≤ ‖(1 : ℂ) - Complex.exp (-z)‖ :=
    abs_norm_sub_norm_le _ _
  rw [norm_one, Complex.norm_exp, Complex.neg_re] at hb
  have hle : Real.exp (-z.re) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have habs : |1 - Real.exp (-z.re)| = 1 - Real.exp (-z.re) := abs_of_nonneg (by linarith)
  rw [habs] at hb
  have h3 := div_one_add_le_one_sub_exp_neg z.re hz
  linarith

/-- The argument of `tauC σ α` at `w = -i s` is `z = 2π s α`. -/
lemma tauC_arg_axis (α : ℂ) (s : ℝ) :
    2 * Real.pi * Complex.I * α * (-((s : ℂ) * Complex.I))
      = ((2 * Real.pi * s : ℝ) : ℂ) * α := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  linear_combination (-(2 * Real.pi * (s : ℂ) * α)) * hI

/-- On the lower axis `w = -i s` the universal cover is bounded by `4/s + 17‖α‖`, uniformly in the
data: with `z = 2π s α` (`Re z > 0`) one has `tauC σ α (-i s) = σ/(1 - e^{-z})`; if `Re z ≤ 1` then
`‖1 - e^{-z}‖ ≥ Re z/2 = π s Re α ≥ π s ‖α‖/√2`, giving `‖τ‖ ≤ 18√2/(7s) ≤ 4/s`, while if
`Re z ≥ 1` then `‖1 - e^{-z}‖ ≥ 1 - 1/e ≥ 1/2`, giving `‖τ‖ ≤ 2‖σ‖ ≤ (36π/7)‖α‖ ≤ 17‖α‖`. -/
theorem tauC_axis_lower {σ α : ℂ} {s : ℝ} (hInF1 : MandelDim.InF1 α) (hs : 0 < s)
    (hσ : ‖σ‖ ≤ 9 / 7 * ‖2 * Real.pi * Complex.I * α‖) :
    ‖Work.Pert.tauC σ α (-((s : ℂ) * Complex.I))‖ ≤ 4 / s + 17 * ‖α‖ := by
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
  have hnorm_sq : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have him : α.im ^ 2 < α.re ^ 2 := by
    have h := abs_lt.mp hInF1
    nlinarith [h.1, h.2]
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- `‖α‖ ≤ √2 Re α` because `|Im α| < Re α`
  have hα_norm_le : ‖α‖ ≤ Real.sqrt 2 * α.re := by
    rw [mul_self_le_mul_self_iff (norm_nonneg α) (mul_nonneg hsqrt2.le hαre.le)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), hnorm_sq, him]
  -- `‖σ‖ ≤ (9/7)·2π‖α‖`
  have hσ_le : ‖σ‖ ≤ 9 / 7 * (2 * Real.pi * ‖α‖) := by
    have h2pi : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_of_nonneg Real.pi_pos.le,
        Complex.norm_I, mul_one]
    have hnorm2pi : ‖2 * Real.pi * Complex.I * α‖ = 2 * Real.pi * ‖α‖ := by
      rw [norm_mul, h2pi]
    rwa [hnorm2pi] at hσ
  -- `‖σ‖ ≤ 8π Re α`
  have hσ4 : ‖σ‖ ≤ 8 * Real.pi * α.re := by
    have h2 : Real.sqrt 2 ≤ 28 / 9 := by
      rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 28 / 9)]
      norm_num
    have hα_le : ‖α‖ ≤ (28 / 9) * α.re := by
      calc ‖α‖ ≤ Real.sqrt 2 * α.re := hα_norm_le
        _ ≤ (28 / 9) * α.re := mul_le_mul_of_nonneg_right h2 hαre.le
    have h3 : (9 / 7) * (2 * Real.pi * ‖α‖) ≤ 8 * Real.pi * α.re := by
      have h4 : (9 / 7) * (2 * Real.pi * ‖α‖) = (18 * Real.pi / 7) * ‖α‖ := by ring
      have h5 : (18 * Real.pi / 7) * ‖α‖ ≤ (18 * Real.pi / 7) * ((28 / 9) * α.re) :=
        mul_le_mul_of_nonneg_left hα_le (by positivity)
      have h6 : (18 * Real.pi / 7) * ((28 / 9) * α.re) = 8 * Real.pi * α.re := by ring
      linarith [h4, h5, h6]
    linarith [hσ_le, h3]
  -- `‖σ‖ ≤ 17‖α‖`
  have hσ17 : ‖σ‖ ≤ 17 * ‖α‖ := by
    have h17 : (9 / 7) * (2 * Real.pi * ‖α‖) ≤ 17 * ‖α‖ := by
      nlinarith [Real.pi_lt_d2, Real.pi_pos, norm_nonneg α]
    linarith [hσ_le, h17]
  have hxpos : 0 < 2 * Real.pi * s * α.re := by positivity
  -- denominator bound
  have hden : (2 * Real.pi * s * α.re) / (1 + 2 * Real.pi * s * α.re)
      ≤ ‖1 - Complex.exp (-(((2 * Real.pi * s : ℝ) : ℂ) * α))‖ := by
    have hzre : ((((2 * Real.pi * s : ℝ) : ℂ) * α)).re = 2 * Real.pi * s * α.re := by
      simp [Complex.mul_re]
    have hz : 0 ≤ ((((2 * Real.pi * s : ℝ) : ℂ) * α)).re := by rw [hzre]; positivity
    have h := le_norm_one_sub_exp_neg_mul (((2 * Real.pi * s : ℝ) : ℂ) * α) hz
    rwa [hzre] at h
  have hdiv : ‖σ‖ / (2 * Real.pi * s * α.re) ≤ 4 / s := by
    rw [div_le_div_iff₀ hxpos hs]
    nlinarith [hσ4, hs]
  have htau : ‖Work.Pert.tauC σ α (-((s : ℂ) * Complex.I))‖
      = ‖σ‖ / ‖1 - Complex.exp (-(((2 * Real.pi * s : ℝ) : ℂ) * α))‖ := by
    rw [Work.Pert.tauC, tauC_arg_axis, norm_div]
  have hx1 : 0 < 1 + 2 * Real.pi * s * α.re := by linarith
  have hsplit : ‖σ‖ / ((2 * Real.pi * s * α.re) / (1 + 2 * Real.pi * s * α.re))
      = ‖σ‖ / (2 * Real.pi * s * α.re) + ‖σ‖ := by
    field_simp
  calc ‖Work.Pert.tauC σ α (-((s : ℂ) * Complex.I))‖
      = ‖σ‖ / ‖1 - Complex.exp (-(((2 * Real.pi * s : ℝ) : ℂ) * α))‖ := htau
    _ ≤ ‖σ‖ / ((2 * Real.pi * s * α.re) / (1 + 2 * Real.pi * s * α.re)) :=
        div_le_div_of_nonneg_left (norm_nonneg σ) (by positivity) hden
    _ = ‖σ‖ / (2 * Real.pi * s * α.re) + ‖σ‖ := hsplit
    _ ≤ 4 / s + 17 * ‖α‖ := add_le_add hdiv hσ17

end Work.Pert.PinLogDev
