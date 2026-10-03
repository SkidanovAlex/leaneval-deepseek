import Mathlib
import Submission.Work.Pert.norm_log_sub_log_le

namespace Work.Pert

/-- The principal branch of the complex logarithm is `4`-Lipschitz on the closed disc of
radius `1/2` about `1` (a disc on which `log` is holomorphic, avoiding the branch cut).
This is the special case `L = 1`, `r = 1/2` of `norm_log_sub_log_le`, where `log 1 = 0`
and `‖1‖ = 1`. -/
theorem norm_log_le_four_mul_of_norm_sub_one_le_half {H : ℂ} (h : ‖H - 1‖ ≤ 1 / 2) :
    ‖Complex.log H‖ ≤ 4 * ‖H - 1‖ := by
  have hmain := norm_log_sub_log_le (L := (1 : ℂ)) (w := H) (r := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) h
  simpa using hmain

end Work.Pert
