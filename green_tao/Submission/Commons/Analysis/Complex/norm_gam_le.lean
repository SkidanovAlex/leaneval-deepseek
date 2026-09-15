import Mathlib
import Submission.Commons.Analysis.Complex.contour_shift_residue

namespace Commons.Analysis.Complex

/-- The absolute value of `phi β t = -β / log (|t| + 2)` for `β > 0`. -/
lemma abs_phi_eq {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    |phi β t| = β / Real.log (|t| + 2) := by
  rw [phi, abs_neg, abs_of_nonneg]
  exact div_nonneg hβ.le (Real.log_nonneg (by have := abs_nonneg t; linarith))

/-- `|φ β t| ≤ β / log 2` for `β > 0`. -/
lemma abs_phi_le {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    |phi β t| ≤ β / Real.log 2 := by
  rw [abs_phi_eq hβ]
  refine div_le_div_of_nonneg_left hβ.le (Real.log_pos (by norm_num)) ?_
  exact Real.log_le_log (by norm_num) (by have := abs_nonneg t; linarith)

/-- Upper bound for `‖gam β t‖`: `‖gam β t‖ ≤ |t| + β / log 2`. -/
theorem norm_gam_le {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    ‖Commons.Analysis.Complex.gam β t‖ ≤ |t| + β / Real.log 2 := by
  have h1 : ‖gam β t‖ ≤ ‖(phi β t : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := by
    simpa only [gam] using norm_add_le ((phi β t : ℂ)) ((t : ℂ) * Complex.I)
  have h2 : ‖(t : ℂ) * Complex.I‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h3 : ‖(phi β t : ℂ)‖ = |phi β t| := Complex.norm_real _
  have h4 : |phi β t| ≤ β / Real.log 2 := abs_phi_le hβ t
  calc ‖gam β t‖ ≤ |phi β t| + |t| := by rw [h3, h2] at h1; exact h1
    _ ≤ β / Real.log 2 + |t| := by linarith
    _ = |t| + β / Real.log 2 := by ring

end Commons.Analysis.Complex
