import Mathlib

namespace Work.Pert

/-- Elementary lower bound for `1 - exp w`: for `‖w‖ ≤ 1`,
`‖w‖ (1 - ‖w‖) ≤ ‖1 - exp w‖`.
Indeed `1 - exp w = -w - (exp w - 1 - w)`, and
`‖exp w - 1 - w‖ ≤ ‖w‖²` (`Complex.norm_exp_sub_one_sub_id_le`). -/
private lemma norm_one_sub_exp_lower {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖w‖ * (1 - ‖w‖) ≤ ‖1 - Complex.exp w‖ := by
  have htail : ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hw
  have hsplit : 1 - Complex.exp w = -w - (Complex.exp w - 1 - w) := by ring
  calc ‖w‖ * (1 - ‖w‖) = ‖w‖ - ‖w‖ ^ 2 := by ring
    _ ≤ ‖w‖ - ‖Complex.exp w - 1 - w‖ := by linarith
    _ = ‖-w‖ - ‖Complex.exp w - 1 - w‖ := by rw [norm_neg]
    _ ≤ ‖-w - (Complex.exp w - 1 - w)‖ := norm_sub_norm_le _ _
    _ = ‖1 - Complex.exp w‖ := by rw [← hsplit]

/-- For `‖α‖ ≤ 1/1024`, `π ‖α‖ ≤ ‖1 - exp (2πi α)‖`.
Since `‖2πi α‖ = 2π‖α‖ ≤ 1/2 ≤ 1`, the quadratic remainder bound gives
`‖1 - exp(2πi α)‖ ≥ ‖2πi α‖ (1 - ‖2πi α‖) = 2π‖α‖ (1 - 2π‖α‖) ≥ π‖α‖`. -/
theorem norm_one_sub_exp_two_pi_I_lower {α : ℂ} (hα : ‖α‖ ≤ 1 / 1024) :
    Real.pi * ‖α‖ ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
  have hwnorm : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ = 2 * Real.pi * ‖α‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_I, mul_one, Complex.norm_ofNat]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hle_half : 2 * Real.pi * ‖α‖ ≤ 1 / 2 := by
    nlinarith [hα, norm_nonneg α, Real.pi_lt_four]
  have hfin : Real.pi * ‖α‖ ≤ (2 * Real.pi * ‖α‖) * (1 - 2 * Real.pi * ‖α‖) := by
    have hs0 : (0:ℝ) ≤ 2 * Real.pi * ‖α‖ := by positivity
    have h1 : (1:ℝ)/2 ≤ 1 - 2 * Real.pi * ‖α‖ := by linarith
    calc Real.pi * ‖α‖ = (2 * Real.pi * ‖α‖) * (1/2) := by ring
      _ ≤ (2 * Real.pi * ‖α‖) * (1 - 2 * Real.pi * ‖α‖) :=
          mul_le_mul_of_nonneg_left h1 hs0
  have hkey := norm_one_sub_exp_lower (w := 2 * Real.pi * Complex.I * α)
    (by rw [hwnorm]; linarith)
  rw [hwnorm] at hkey
  linarith [hkey, hfin]

end Work.Pert
