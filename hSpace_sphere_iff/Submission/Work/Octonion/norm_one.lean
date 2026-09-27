import Mathlib
import Submission.Work.Octonion.Basic

namespace Work.Octonion

theorem norm_one : ‖(1 : Submission.Octonion)‖ = 1 := by
  have h : (1 : Submission.Octonion) =
      WithLp.toLp 2 ((1 : Quaternion ℝ), (0 : Quaternion ℝ)) := rfl
  rw [h, WithLp.prod_norm_eq_of_L2]
  norm_num

end Work.Octonion
