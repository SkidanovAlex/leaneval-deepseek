import Mathlib
import Submission.Work.Pert.exp_alpha_bounds

/-- The statement below writes the imaginary unit as the bare token `I`, which is
*not* a notation in this Mathlib (only `Complex.I` is; `I` is a `unitInterval`
notation, scoped).  We resolve the intended meaning — the imaginary unit — locally,
so that the statement is read exactly as written while elaborating. -/
local notation "I" => Complex.I

namespace Work.PertCrux

/-- For `0 < ‖w‖ ≤ 1`, the first-order remainder of `(exp w - 1)/w` is bounded by
`‖w‖`.  This is the "quotient" form of the quadratic remainder estimate
`‖exp w - 1 - w‖ ≤ ‖w‖²`. -/
private lemma norm_exp_div_sub_one_le {w : ℂ} (hw1 : ‖w‖ ≤ 1) (hw0 : w ≠ 0) :
    ‖(Complex.exp w - 1) / w - 1‖ ≤ ‖w‖ := by
  have h : (Complex.exp w - 1) / w - 1 = (Complex.exp w - 1 - w) / w := by
    rw [← div_self hw0, ← sub_div]
  rw [h, norm_div]
  have hle := Complex.norm_exp_sub_one_sub_id_le hw1
  rw [div_le_iff₀ (norm_pos_iff.mpr hw0)]
  calc ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := hle
    _ = ‖w‖ * ‖w‖ := by ring

theorem exp_remainder_mul_le {α X : ℂ} {η : ℝ}
    (hα : α ≠ 0) (hη : 0 < η) (hη1 : η ≤ 1 / 1000) (hαη : ‖α‖ ≤ η) (hX : ‖X‖ ≤ 7 / 2) :
    ‖((Complex.exp (2 * Real.pi * Complex.I * α) - 1) / (2 * Real.pi * I * α) - 1) * X‖
      ≤ 28 * η := by
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hznorm : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ = 2 * Real.pi * ‖α‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    have hI : ‖Complex.I‖ = 1 := Complex.norm_I
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h2c : ‖(2 : ℂ)‖ = 2 := by
      rw [Complex.norm_def, Complex.normSq_apply]; norm_num
    rw [h2c, hp, hI, mul_one]
  have hz0 : (2 * Real.pi * Complex.I * α : ℂ) ≠ 0 := by
    rw [← norm_pos_iff, hznorm]; positivity
  have hz1 : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ ≤ 1 := by
    rw [hznorm]
    nlinarith [hαη, hη1, hαpos, hη, Real.pi_pos, Real.pi_le_four]
  have key :
      ‖(Complex.exp (2 * Real.pi * Complex.I * α) - 1) / (2 * Real.pi * Complex.I * α) - 1‖
        ≤ 2 * Real.pi * ‖α‖ := by
    calc ‖(Complex.exp (2 * Real.pi * Complex.I * α) - 1)
            / (2 * Real.pi * Complex.I * α) - 1‖
        ≤ ‖(2 * Real.pi * Complex.I * α : ℂ)‖ :=
          norm_exp_div_sub_one_le hz1 hz0
      _ = 2 * Real.pi * ‖α‖ := hznorm
  rw [norm_mul]
  calc ‖(Complex.exp (2 * Real.pi * Complex.I * α) - 1)
          / (2 * Real.pi * Complex.I * α) - 1‖ * ‖X‖
      ≤ (2 * Real.pi * ‖α‖) * (7 / 2) := by
        apply mul_le_mul key hX (norm_nonneg X) (by positivity)
    _ = 7 * Real.pi * ‖α‖ := by ring
    _ ≤ 7 * Real.pi * η := by nlinarith [Real.pi_pos, hαη]
    _ ≤ 28 * η := by nlinarith [Real.pi_le_four, hη]

end Work.PertCrux
