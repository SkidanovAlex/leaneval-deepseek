import Mathlib
import Submission.Work.Pert.norm_exp_sub_one_sub_id_le_sharp

namespace Work.Pert

/-- **Bound on `z / (1 - exp (-z))` for small `z`.**

For `z ≠ 0` with `‖z‖ ≤ 3/64` we have `‖z / (1 - exp (-z))‖ ≤ 1.04`.

The quantity `z/(1 - exp(-z))` equals `1/(1 - z/2 + z²/6 - …)`, so it is `1 + O(‖z‖)`.
Writing `1 - exp(-z) = z + w` with `‖w‖ = ‖exp(-z) - 1 - (-z)‖ ≤ (29/48) ‖z‖²`
(`norm_exp_sub_one_sub_id_le_sharp`, legitimate as `‖z‖ ≤ 3/64 ≤ 1/2`), the reverse triangle
inequality gives

  `‖1 - exp(-z)‖ ≥ ‖z‖ - (29/48) ‖z‖² ≥ (995/1024) ‖z‖`,

the last step using `(29/48) ‖z‖² ≤ (29/1024) ‖z‖` for `‖z‖ ≤ 3/64`. Hence

  `‖z/(1 - exp(-z))‖ = ‖z‖ / ‖1 - exp(-z)‖ ≤ 1024/995 ≤ 1.04`. -/
theorem norm_div_one_sub_exp_neg_le {z : ℂ} (hz : z ≠ 0) (hzle : ‖z‖ ≤ 3 / 64) :
    ‖z / (1 - Complex.exp (-z))‖ ≤ 1.04 := by
  have hzpos : 0 < ‖z‖ := by rw [norm_pos_iff]; exact hz
  have hhalf : ‖(-z)‖ ≤ 1 / 2 := by rw [norm_neg]; linarith
  have hsharp := norm_exp_sub_one_sub_id_le_sharp (z := -z) hhalf
  rw [norm_neg] at hsharp
  -- `‖1 - exp(-z) - z‖ = ‖exp(-z) - 1 - (-z)‖ ≤ (29/48) ‖z‖²`
  have hnum : ‖1 - Complex.exp (-z) - z‖ ≤ 29 / 48 * ‖z‖ ^ 2 := by
    have heq : 1 - Complex.exp (-z) - z = -(Complex.exp (-z) - 1 - -z) := by ring
    rw [heq, norm_neg]
    exact hsharp
  -- Reverse triangle inequality: `‖z‖ ≤ ‖1 - exp(-z)‖ + ‖1 - exp(-z) - z‖`.
  have hrev : ‖z‖ ≤ ‖1 - Complex.exp (-z)‖ + ‖1 - Complex.exp (-z) - z‖ := by
    have h := norm_sub_le (z + (1 - Complex.exp (-z) - z)) (1 - Complex.exp (-z) - z)
    rw [show z + (1 - Complex.exp (-z) - z) - (1 - Complex.exp (-z) - z) = z by ring,
        show z + (1 - Complex.exp (-z) - z) = 1 - Complex.exp (-z) by ring] at h
    exact h
  have hden : ‖z‖ - 29 / 48 * ‖z‖ ^ 2 ≤ ‖1 - Complex.exp (-z)‖ := by linarith
  -- `(29/48) ‖z‖² ≤ (29/1024) ‖z‖` from `‖z‖ ≤ 3/64`.
  have hsq : 29 / 48 * ‖z‖ ^ 2 ≤ (29 / 1024) * ‖z‖ := by
    have h2 : ‖z‖ ^ 2 ≤ (3 / 64) * ‖z‖ := by
      calc ‖z‖ ^ 2 = ‖z‖ * ‖z‖ := by ring
        _ ≤ ‖z‖ * (3 / 64) := mul_le_mul_of_nonneg_left hzle hzpos.le
        _ = (3 / 64) * ‖z‖ := by ring
    nlinarith [h2, hzpos.le]
  have hden_lb : (995 / 1024) * ‖z‖ ≤ ‖1 - Complex.exp (-z)‖ := by
    nlinarith [hden, hsq]
  have hden_pos : 0 < ‖1 - Complex.exp (-z)‖ :=
    lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 995 / 1024) hzpos) hden_lb
  rw [Complex.norm_div, div_le_iff₀ hden_pos]
  have step1 : (1.04 : ℝ) * ((995 / 1024) * ‖z‖) ≤ 1.04 * ‖1 - Complex.exp (-z)‖ :=
    mul_le_mul_of_nonneg_left hden_lb (by norm_num)
  have step2 : ‖z‖ ≤ (1.04 : ℝ) * ((995 / 1024) * ‖z‖) := by
    nlinarith [hzpos.le]
  linarith [step1, step2]

end Work.Pert
