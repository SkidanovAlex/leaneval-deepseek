import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.norm_log_le_three_add_pi
import Submission.Work.Pert.norm_log_le_four_mul_of_norm_sub_one_le_half

namespace Work.Pert

/-- If `H` is within `1000 * a * (1 + R) * d` of `1` and lies in the annulus `1/4 ≤ ‖H‖ ≤ 2`,
then `‖log H‖ ≤ 2π·2¹¹·a·(1+R)·d`.

The proof splits on the size of `s = a·(1+R)·d`.  If `1000 s ≤ 1/2` then `H` is in the disc of
radius `1/2` around `1`, where `log` is `4`-Lipschitz (`norm_log_le_four_mul_of_norm_sub_one_le_half`),
so `‖log H‖ ≤ 4·‖H-1‖ ≤ 4000 s ≤ 4096 π s`.  Otherwise `s ≥ 1/2000`, and the crude annulus bound
`‖log H‖ ≤ 3 + π` (`norm_log_le_three_add_pi`) is already below `4096 π ·(1/2000) = 2.048 π`. -/
theorem log_close_one_le {H : ℂ} {a d R : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hlo : 1 / 4 ≤ ‖H‖) (hhi : ‖H‖ ≤ 2)
    (hclose : ‖H - 1‖ ≤ 1000 * a * (1 + R) * d) :
    ‖Complex.log H‖ ≤ 2 * Real.pi * 2 ^ 11 * a * (1 + R) * d := by
  have hR1 : (0 : ℝ) ≤ 1 + R := by linarith
  have hs : 0 ≤ a * (1 + R) * d := mul_nonneg (mul_nonneg ha hR1) hd
  set s : ℝ := a * (1 + R) * d with hsdef
  have hbound : ‖H - 1‖ ≤ 1000 * s := by rw [hsdef]; linarith
  have hRHS : 2 * Real.pi * 2 ^ 11 * a * (1 + R) * d = 4096 * Real.pi * s := by
    rw [hsdef]; norm_num; ring
  rw [hRHS]
  by_cases hc : 1000 * s ≤ 1 / 2
  · -- `H` is within `1/2` of `1`: use the local Lipschitz bound.
    have h1 : ‖H - 1‖ ≤ 1 / 2 := le_trans hbound hc
    have h2 : ‖Complex.log H‖ ≤ 4 * ‖H - 1‖ :=
      norm_log_le_four_mul_of_norm_sub_one_le_half h1
    have h4 : 4 * ‖H - 1‖ ≤ 4000 * s := by
      have h := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    have h5 : (4000 : ℝ) ≤ 4096 * Real.pi := by linarith [Real.pi_gt_three]
    calc ‖Complex.log H‖ ≤ 4 * ‖H - 1‖ := h2
      _ ≤ 4000 * s := h4
      _ ≤ 4096 * Real.pi * s := mul_le_mul_of_nonneg_right h5 hs
  · -- `s ≥ 1/2000`: the crude annulus bound already suffices.
    have hc' : 1 / 2 < 1000 * s := not_le.mp hc
    have hs1 : 1 / 2000 ≤ s := by linarith
    have hann : ‖Complex.log H‖ ≤ 3 + Real.pi := norm_log_le_three_add_pi hlo hhi
    have hp : 3 + Real.pi ≤ 2.048 * Real.pi := by linarith [Real.pi_gt_three]
    have h4 : (2.048 : ℝ) * Real.pi ≤ 4096 * Real.pi * s := by
      have h5 : 4096 * Real.pi * (1 / 2000) ≤ 4096 * Real.pi * s :=
        mul_le_mul_of_nonneg_left hs1 (by positivity)
      have h6 : 4096 * Real.pi * (1 / 2000) = 2.048 * Real.pi := by norm_num; ring
      linarith
    linarith

end Work.Pert
