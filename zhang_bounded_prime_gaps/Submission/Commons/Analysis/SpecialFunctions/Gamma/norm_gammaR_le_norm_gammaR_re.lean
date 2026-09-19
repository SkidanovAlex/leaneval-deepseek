import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_Gamma_le_norm_Gamma_re
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_vertical_lower_any

open Complex
set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- Real part of a half: `(s / 2).re = s.re / 2`. -/
lemma re_of_half (s : ℂ) : (s / 2).re = s.re / 2 := by
  rw [Complex.div_re]
  norm_num
  ring

/-- Vertical bound for Deligne's real Gamma factor: for `0 < Re s`,
`‖Gammaℝ s‖ ≤ ‖Gammaℝ (Re s)‖` where `Gammaℝ s = π^(-s/2) · Γ(s/2)`. -/
theorem norm_gammaR_le_norm_gammaR_re (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gammaℝ s‖ ≤ ‖Complex.Gammaℝ (s.re : ℂ)‖ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  rw [norm_mul, norm_mul]
  rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos, norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have h1 : (-s / 2).re = -s.re / 2 := by
    rw [Complex.div_re, Complex.neg_re]
    norm_num
    ring
  have h2 : (-(s.re : ℂ) / 2).re = -s.re / 2 := by
    rw [Complex.div_re, Complex.neg_re]
    norm_num
    ring
  rw [h1, h2]
  have hpos : 0 < (s / 2).re := by
    rw [re_of_half]
    exact div_pos hs (by norm_num)
  have h := norm_Gamma_le_norm_Gamma_re (s / 2) hpos
  have hArg : ((s / 2).re : ℂ) = (s.re : ℂ) / 2 := by
    rw [re_of_half]
    rw [Complex.ofReal_div]
    rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
  have hΓ : ‖Complex.Gamma (s / 2)‖ ≤ ‖Complex.Gamma ((s.re : ℂ) / 2)‖ := by
    simpa [hArg] using h
  exact mul_le_mul_of_nonneg_left hΓ (Real.rpow_nonneg (le_of_lt Real.pi_pos) _)

end Commons.Analysis.SpecialFunctions.Gamma
