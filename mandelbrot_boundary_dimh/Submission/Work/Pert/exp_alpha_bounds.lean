import Mathlib

namespace Work.Pert

/-- For `‖z‖ ≤ 1` and `z ≠ 0`, `‖(exp z - 1)/z - 1‖ ≤ ‖z‖`.
This is the "quotient" form of the quadratic remainder estimate
`‖exp z - 1 - z‖ ≤ ‖z‖²` of Mathlib. -/
private lemma norm_exp_div_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1) (hz0 : z ≠ 0) :
    ‖(Complex.exp z - 1) / z - 1‖ ≤ ‖z‖ := by
  have h : (Complex.exp z - 1) / z - 1 = (Complex.exp z - 1 - z) / z := by
    rw [← div_self hz0, ← sub_div]
  rw [h, norm_div]
  have hle := Complex.norm_exp_sub_one_sub_id_le hz
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [div_le_iff₀ hpos]
  calc ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 := hle
    _ = ‖z‖ * ‖z‖ := by ring

theorem exp_alpha_bounds {α : ℂ} (hα : α ≠ 0) (h2 : 2 * Real.pi * ‖α‖ ≤ 1) :
    ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1 - 2 * Real.pi * Complex.I * α‖
        ≤ 4 * Real.pi ^ 2 * ‖α‖ ^ 2 ∧
    ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖ ≤ 4 * Real.pi * ‖α‖ ∧
    ‖(Complex.exp (2 * Real.pi * Complex.I * α) - 1) / (2 * Real.pi * Complex.I * α) - 1‖
        ≤ 4 * Real.pi * ‖α‖ := by
  set z : ℂ := 2 * Real.pi * Complex.I * α with hzdef
  have hznorm : ‖z‖ = 2 * Real.pi * ‖α‖ := by
    rw [hzdef, norm_mul, norm_mul, norm_mul]
    have hI : ‖Complex.I‖ = 1 := Complex.norm_I
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h2c : ‖(2 : ℂ)‖ = 2 := by
      rw [Complex.norm_def, Complex.normSq_apply]; norm_num
    rw [h2c, hp, hI, mul_one]
  have hz0 : z ≠ 0 := by
    rw [hzdef]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) hα
    · norm_num
    · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    · exact Complex.I_ne_zero
  have hz1 : ‖z‖ ≤ 1 := by rw [hznorm]; exact h2
  refine ⟨?_, ?_, ?_⟩
  · calc ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hz1
      _ = 4 * Real.pi ^ 2 * ‖α‖ ^ 2 := by rw [hznorm]; ring
  · calc ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := Complex.norm_exp_sub_one_le hz1
      _ = 4 * Real.pi * ‖α‖ := by rw [hznorm]; ring
  · calc ‖(Complex.exp z - 1) / z - 1‖ ≤ ‖z‖ := norm_exp_div_sub_one_le hz1 hz0
      _ = 2 * Real.pi * ‖α‖ := hznorm
      _ ≤ 4 * Real.pi * ‖α‖ := by nlinarith [Real.pi_pos, norm_nonneg α]

end Work.Pert
