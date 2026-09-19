import Mathlib.Analysis.Complex.Trigonometric
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.norm_cosh_ofReal

namespace Commons.Analysis.SpecialFunctions.Trigonometric

theorem norm_sinh_ofReal (y : ℝ) : ‖Complex.sinh (y : ℂ)‖ = |Real.sinh y| := by
  rw [← Complex.ofReal_sinh]
  rw [Complex.norm_real]
  exact Real.norm_eq_abs _

end Commons.Analysis.SpecialFunctions.Trigonometric