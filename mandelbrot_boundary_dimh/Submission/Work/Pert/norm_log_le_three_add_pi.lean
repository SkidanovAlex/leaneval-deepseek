import Mathlib

namespace Work.Pert

/-- For `H` with `1/4 ≤ ‖H‖ ≤ 2`, the complex logarithm is small:
`log H = log ‖H‖ + i·arg H`, with `|log ‖H‖| ≤ log 4 ≤ 3` and `|arg H| ≤ π`. -/
theorem norm_log_le_three_add_pi {H : ℂ} (hlo : 1 / 4 ≤ ‖H‖) (hhi : ‖H‖ ≤ 2) :
    ‖Complex.log H‖ ≤ 3 + Real.pi := by
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hx : 0 < ‖H‖ := lt_of_lt_of_le (by norm_num) hlo
  have hre_le : |(Complex.log H).re| ≤ Real.log 4 := by
    rw [Complex.log_re]
    have h1 : Real.log ‖H‖ ≤ Real.log 4 := Real.log_le_log hx (by linarith)
    have h2 : -Real.log 4 ≤ Real.log ‖H‖ := by
      have h : Real.log (1 / 4 : ℝ) ≤ Real.log ‖H‖ := Real.log_le_log (by norm_num) hlo
      rw [one_div, Real.log_inv] at h
      linarith
    exact abs_le.mpr ⟨h2, h1⟩
  have him_le : |(Complex.log H).im| ≤ Real.pi := by
    rw [Complex.log_im]
    exact abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg H), Complex.arg_le_pi H⟩
  calc ‖Complex.log H‖ ≤ |(Complex.log H).re| + |(Complex.log H).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ Real.log 4 + Real.pi := add_le_add hre_le him_le
    _ ≤ 3 + Real.pi := by linarith

end Work.Pert
