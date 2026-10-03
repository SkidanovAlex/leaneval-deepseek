import Mathlib

namespace Work.Pert.TauCGate

/-- Elementary lower bound for `1 - exp w`: for `‖w‖ ≤ 1`,
`‖w‖ (1 - ‖w‖) ≤ ‖1 - exp w‖`.
Indeed `1 - exp w = -w - (exp w - 1 - w)` and `‖exp w - 1 - w‖ ≤ ‖w‖²`. -/
private lemma norm_one_sub_exp_lower {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖w‖ * (1 - ‖w‖) ≤ ‖1 - Complex.exp w‖ := by
  have htail : ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hw
  have hsplit : 1 - Complex.exp w = -w - (Complex.exp w - 1 - w) := by ring
  calc ‖w‖ * (1 - ‖w‖) = ‖w‖ - ‖w‖ ^ 2 := by ring
    _ ≤ ‖w‖ - ‖Complex.exp w - 1 - w‖ := by linarith
    _ = ‖-w‖ - ‖Complex.exp w - 1 - w‖ := by rw [norm_neg]
    _ ≤ ‖-w - (Complex.exp w - 1 - w)‖ := norm_sub_norm_le _ _
    _ = ‖1 - Complex.exp w‖ := by rw [← hsplit]

/-- Numerical fact: `28/5 ≤ 2π (1 - π/32)`, i.e. `28/5 ≤ 2π - π²/16`. -/
private lemma pi_arith : (28 : ℝ) / 5 ≤ 2 * Real.pi - Real.pi ^ 2 / 16 := by
  nlinarith [Real.pi_gt_d2, Real.pi_lt_d2]

/-- Quantitative lower bound for the gate map: if `‖α‖ ≤ 1/64` then
`(28/5) ‖α‖ ≤ ‖1 - exp (2πi α)‖`.  The series bound `‖1 - exp w‖ ≥ ‖w‖ (1 - ‖w‖)`
applied to `w = 2πi α` (of norm `2π‖α‖ ≤ π/32`) gives the claim since
`2π (1 - π/32) ≥ 28/5`. -/
theorem one_sub_exp_two_pi_I_ge {α : ℂ} (hα : ‖α‖ ≤ 1 / 64) :
    (28 / 5) * ‖α‖ ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
  have hwnorm : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ = 2 * Real.pi * ‖α‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_I, mul_one, Complex.norm_ofNat]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hle : 2 * Real.pi * ‖α‖ ≤ 1 := by
    nlinarith [hα, norm_nonneg α, Real.pi_lt_four, Real.pi_pos]
  have hkey := norm_one_sub_exp_lower (w := (2 * Real.pi * Complex.I * α : ℂ))
    (by rw [hwnorm]; exact hle)
  rw [hwnorm] at hkey
  have ht0 : (0 : ℝ) ≤ ‖α‖ := norm_nonneg α
  have hrt : 2 * Real.pi * ‖α‖ ≤ Real.pi / 32 := by
    nlinarith [hα, norm_nonneg α, Real.pi_pos]
  have hstep : (28 / 5) * ‖α‖ ≤ (2 * Real.pi * ‖α‖) * (1 - 2 * Real.pi * ‖α‖) := by
    have hA : (2 * Real.pi * ‖α‖) * (1 - Real.pi / 32)
        ≤ (2 * Real.pi * ‖α‖) * (1 - 2 * Real.pi * ‖α‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [hrt]
    have hB : (2 * Real.pi * ‖α‖) * (1 - Real.pi / 32)
        = ‖α‖ * (2 * Real.pi - Real.pi ^ 2 / 16) := by ring
    have hC : ‖α‖ * ((28 : ℝ) / 5) ≤ ‖α‖ * (2 * Real.pi - Real.pi ^ 2 / 16) :=
      mul_le_mul_of_nonneg_left pi_arith ht0
    linarith [hA, hB, hC]
  linarith [hkey, hstep]

end Work.Pert.TauCGate
