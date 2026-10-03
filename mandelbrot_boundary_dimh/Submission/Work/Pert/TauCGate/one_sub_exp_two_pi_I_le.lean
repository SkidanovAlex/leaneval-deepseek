import Mathlib

namespace Work.Pert.TauCGate

/-- **Ratio bound for `1 - exp (2πi α)` near `α = 0`.**

For `‖α‖ ≤ 1/64`, `‖1 - exp (2πi α)‖ ≤ (36/5) ‖α‖`.

Proof: put `w = 2πi α`, so `‖w‖ = 2π ‖α‖ ≤ π/32 ≤ 1`.  The quadratic Taylor bound
`Complex.norm_exp_sub_one_sub_id_le` gives `‖exp w - 1 - w‖ ≤ ‖w‖²`, hence
`‖1 - exp w‖ ≤ ‖w‖ + ‖w‖²`.  Since `‖w‖ ≤ π/32`, the square is dominated by
`(π/32) ‖w‖`, so `‖1 - exp w‖ ≤ (1 + π/32) ‖w‖ = 2π (1 + π/32) ‖α‖`,
and `2π (1 + π/32) = 2π + π²/16 < 6.93 < 36/5` by `π < 3.15`. -/
theorem one_sub_exp_two_pi_I_le {α : ℂ} (hα : ‖α‖ ≤ 1 / 64) :
    ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ ≤ (36 / 5) * ‖α‖ := by
  set w : ℂ := 2 * Real.pi * Complex.I * α with hwdef
  have hwnorm : ‖w‖ = 2 * Real.pi * ‖α‖ := by
    rw [hwdef, norm_mul, norm_mul, norm_mul]
    rw [Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hwle1 : ‖w‖ ≤ 1 := by
    rw [hwnorm]
    nlinarith [hα, norm_nonneg α, Real.pi_lt_four]
  have hwle : ‖w‖ ≤ Real.pi / 32 := by
    rw [hwnorm]
    nlinarith [hα, norm_nonneg α, Real.pi_pos]
  have hkey : ‖1 - Complex.exp w‖ ≤ ‖w‖ + ‖w‖ ^ 2 := by
    have htail := Complex.norm_exp_sub_one_sub_id_le hwle1
    have hdecomp : (1 : ℂ) - Complex.exp w = -(Complex.exp w - 1 - w) - w := by ring
    calc ‖1 - Complex.exp w‖ = ‖-(Complex.exp w - 1 - w) - w‖ := by rw [hdecomp]
      _ ≤ ‖-(Complex.exp w - 1 - w)‖ + ‖w‖ := norm_sub_le _ _
      _ = ‖Complex.exp w - 1 - w‖ + ‖w‖ := by rw [norm_neg]
      _ ≤ ‖w‖ ^ 2 + ‖w‖ := by linarith
      _ = ‖w‖ + ‖w‖ ^ 2 := by ring
  have hsq : ‖w‖ ^ 2 ≤ (Real.pi / 32) * ‖w‖ := by
    calc ‖w‖ ^ 2 = ‖w‖ * ‖w‖ := by ring
      _ ≤ ‖w‖ * (Real.pi / 32) := mul_le_mul_of_nonneg_left hwle (norm_nonneg w)
      _ = (Real.pi / 32) * ‖w‖ := by ring
  have hnum : (1 + Real.pi / 32) * (2 * Real.pi) ≤ 36 / 5 := by
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  calc ‖1 - Complex.exp w‖
      ≤ ‖w‖ + ‖w‖ ^ 2 := hkey
    _ ≤ ‖w‖ + (Real.pi / 32) * ‖w‖ := by linarith
    _ = (1 + Real.pi / 32) * ‖w‖ := by ring
    _ = (1 + Real.pi / 32) * (2 * Real.pi * ‖α‖) := by rw [hwnorm]
    _ = ((1 + Real.pi / 32) * (2 * Real.pi)) * ‖α‖ := by ring
    _ ≤ (36 / 5) * ‖α‖ := mul_le_mul_of_nonneg_right hnum (norm_nonneg α)

end Work.Pert.TauCGate
