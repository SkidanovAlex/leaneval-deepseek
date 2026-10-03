import Mathlib

namespace Work.Parab.coverCone

theorem norm_log_le_abs_log_add_pi (u : ℂ) :
    ‖Complex.log u‖ ≤ |Real.log ‖u‖| + Real.pi := by
  calc ‖Complex.log u‖
      ≤ |(Complex.log u).re| + |(Complex.log u).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖u‖| + |(Complex.log u).im| := by rw [Complex.log_re]
    _ ≤ |Real.log ‖u‖| + Real.pi := by
        gcongr
        rw [abs_le]
        exact ⟨le_of_lt (Complex.neg_pi_lt_log_im u), Complex.log_im_le_pi u⟩

end Work.Parab.coverCone
