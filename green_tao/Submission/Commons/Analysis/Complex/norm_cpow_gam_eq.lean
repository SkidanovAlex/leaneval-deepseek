import Mathlib
import Submission.Commons.Analysis.Complex.contour_shift_residue

namespace Commons.Analysis.Complex

/-- The real part of `gam β t` is `phi β t = -β / log (|t| + 2)`. -/
lemma gam_re (β t : ℝ) : (gam β t).re = -(β / Real.log (|t| + 2)) := by
  simp [gam, phi]

/-- The norm of `(R : ℂ) ^ (gam β t)`, for `R > 0`, equals `exp(-(β log R)/log(|t|+2))`. -/
theorem norm_cpow_gam_eq {β R : ℝ} (hR : 0 < R) (t : ℝ) :
    ‖(R : ℂ) ^ (Commons.Analysis.Complex.gam β t)‖
      = Real.exp (-(β * Real.log R) / Real.log (|t| + 2)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hR, gam_re, Real.rpow_def_of_pos hR]
  congr 1
  have hL : Real.log (|t| + 2) ≠ 0 := ne_of_gt (phi_log_pos t)
  field_simp

end Commons.Analysis.Complex
