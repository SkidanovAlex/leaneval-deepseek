import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

/-- `‖exp z - 1‖ ≤ 2‖z‖` for `‖z‖ ≤ 1` applied at `z = 2πi e`, where `‖2πi e‖ = 2π‖e‖ ≤ 2πδ`.
The hypothesis `δ ≤ 1/(16π)` makes `2πδ ≤ 1/8 ≤ 1`. -/
theorem piExp_sub_one_bound {e : ℂ} {δ : ℝ} (hδ : δ ≤ 1 / (16 * Real.pi)) (he : ‖e‖ ≤ δ) :
    ‖piExp e - 1‖ ≤ 4 * Real.pi * δ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnorm : ‖(2 * Real.pi * I * e : ℂ)‖ = 2 * Real.pi * ‖e‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg hpi.le]
    norm_num
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hsmall : ‖(2 * Real.pi * I * e : ℂ)‖ ≤ 1 := by
    rw [hnorm]
    calc 2 * Real.pi * ‖e‖ ≤ 2 * Real.pi * δ := mul_le_mul_of_nonneg_left he h2pi
      _ ≤ 2 * Real.pi * (1 / (16 * Real.pi)) := mul_le_mul_of_nonneg_left hδ h2pi
      _ = 1 / 8 := by field_simp; ring
      _ ≤ 1 := by norm_num
  have hexp := Complex.norm_exp_sub_one_le hsmall
  calc ‖piExp e - 1‖ = ‖Complex.exp (2 * Real.pi * I * e) - 1‖ := by simp only [piExp]
    _ ≤ 2 * ‖(2 * Real.pi * I * e : ℂ)‖ := hexp
    _ = 2 * (2 * Real.pi * ‖e‖) := by rw [hnorm]
    _ = 4 * Real.pi * ‖e‖ := by ring
    _ ≤ 4 * Real.pi * δ := mul_le_mul_of_nonneg_left he (by positivity)

end Work.Repel
