import Mathlib

namespace Work.LinnikAreas.A5

/-- For `x > 0`, the hyperbolic cotangent is bounded by `1 + 1 / x`:
`cosh x / sinh x ≤ 1 + 1 / x`.

This is the elementary estimate `coth x = 1 + e^{-2x}/(1 - e^{-2x}) ≤ 1 + 1/x`,
proved here via `2 x + 1 ≤ exp (2 x)`. -/
lemma coth_le_one_add_inv (x : ℝ) (hx : 0 < x) :
    Real.cosh x / Real.sinh x ≤ 1 + 1 / x := by
  have hsinh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  rw [div_le_iff₀ hsinh]
  have hcosh : Real.cosh x = Real.sinh x + Real.exp (-x) := by
    have h := Real.cosh_sub_sinh x; linarith
  have hkey : Real.exp (-x) ≤ Real.sinh x / x := by
    rw [le_div_iff₀ hx]
    have h1 : 2 * x + 1 ≤ Real.exp (2 * x) := Real.add_one_le_exp (2 * x)
    have h2 : Real.exp (2 * x) * Real.exp (-x) = Real.exp x := by
      rw [← Real.exp_add]; ring_nf
    have hmul : (2 * x + 1) * Real.exp (-x) ≤ Real.exp x := by
      rw [← h2]; exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-x)).le
    have hL : (2 * x + 1) * Real.exp (-x) = 2 * x * Real.exp (-x) + Real.exp (-x) := by ring
    rw [hL] at hmul
    have hmain : x * Real.exp (-x) ≤ Real.sinh x := by
      rw [Real.sinh_eq]; linarith
    linarith
  rw [hcosh]
  have : (1 + 1 / x) * Real.sinh x = Real.sinh x + Real.sinh x / x := by ring
  rw [this]; linarith

theorem wc_tanh_bound (K lam : ℝ) (hK : 0 < K) (hlam : 0 < lam) :
    lam * Real.cosh (K * lam) / Real.sinh (K * lam) ≤ 1 / K + lam := by
  have hx : 0 < K * lam := mul_pos hK hlam
  have hcoth := coth_le_one_add_inv (K * lam) hx
  have hstep : lam * (Real.cosh (K * lam) / Real.sinh (K * lam)) ≤
      lam * (1 + 1 / (K * lam)) := mul_le_mul_of_nonneg_left hcoth hlam.le
  have heq : lam * (1 + 1 / (K * lam)) = 1 / K + lam := by
    field_simp
    ring
  rw [mul_div_assoc]
  rw [heq] at hstep
  exact hstep

end Work.LinnikAreas.A5
