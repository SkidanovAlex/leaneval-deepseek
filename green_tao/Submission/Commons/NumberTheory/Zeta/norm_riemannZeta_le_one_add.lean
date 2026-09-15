import Mathlib.NumberTheory.LSeries.Dirichlet
import Submission.Commons.NumberTheory.Zeta.norm_riemannZeta_le_re
import Submission.Commons.NumberTheory.Zeta.riemannZeta_norm_antitone_re
import Submission.Commons.NumberTheory.Zeta.re_riemannZeta_ofReal_pos

open Complex
open scoped ComplexOrder

namespace Commons.NumberTheory.Zeta

theorem norm_riemannZeta_le_one_add {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 + a ≤ s.re) :
    ‖riemannZeta s‖ ≤ (riemannZeta ((1 + a : ℝ) : ℂ)).re := by
  have h1a : (1 : ℝ) < 1 + a := by linarith
  have hσ : (1 : ℝ) < s.re := lt_of_lt_of_le h1a hs
  -- at the real point `1 + a > 1`, `ζ` is a nonnegative real number, so norm = re
  have hnorm : ‖riemannZeta ((1 + a : ℝ) : ℂ)‖ = (riemannZeta ((1 + a : ℝ) : ℂ)).re := by
    have hpos : 0 ≤ riemannZeta ((1 + a : ℝ) : ℂ) :=
      le_of_lt (riemannZeta_pos_of_one_lt h1a)
    have h : ((‖riemannZeta ((1 + a : ℝ) : ℂ)‖ : ℝ) : ℂ) = riemannZeta ((1 + a : ℝ) : ℂ) :=
      Complex.norm_of_nonneg' hpos
    simpa using congrArg Complex.re h
  calc ‖riemannZeta s‖
      ≤ (riemannZeta ((s.re : ℝ) : ℂ)).re := norm_riemannZeta_le_re hσ
    _ ≤ ‖riemannZeta ((s.re : ℝ) : ℂ)‖ := Complex.re_le_norm _
    _ ≤ ‖riemannZeta ((1 + a : ℝ) : ℂ)‖ := riemannZeta_norm_antitone_re h1a hs
    _ = (riemannZeta ((1 + a : ℝ) : ℂ)).re := hnorm

end Commons.NumberTheory.Zeta