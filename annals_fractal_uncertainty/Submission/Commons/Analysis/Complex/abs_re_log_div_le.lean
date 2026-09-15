import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Complex

namespace Commons.Analysis.Complex

/-- The real part of `log ((1+u)/(1-u))` is bounded by `log ((1+r)/(1-r))` for `‖u‖ ≤ r < 1`. -/
theorem abs_re_log_div_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {u : ℂ} (hu : ‖u‖ ≤ r) :
    |(Complex.log ((1 + u) / (1 - u))).re| ≤ Real.log ((1 + r) / (1 - r)) := by
  have hr1pos : 0 < 1 - r := by linarith
  have hr1pos' : 0 < 1 + r := by linarith
  have hnum_le : ‖(1 : ℂ) + u‖ ≤ 1 + r := by
    calc ‖(1 : ℂ) + u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_add_le _ _
      _ = 1 + ‖u‖ := by rw [norm_one]
      _ ≤ 1 + r := by linarith
  have hnum_ge : 1 - r ≤ ‖(1 : ℂ) + u‖ := by
    have h : ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) + u‖ + ‖u‖ := by
      calc ‖(1 : ℂ)‖ = ‖((1 : ℂ) + u) - u‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖(1 : ℂ) + u‖ + ‖u‖ := norm_sub_le _ _
    rw [norm_one] at h
    linarith
  have hden_le : ‖(1 : ℂ) - u‖ ≤ 1 + r := by
    calc ‖(1 : ℂ) - u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_sub_le _ _
      _ = 1 + ‖u‖ := by rw [norm_one]
      _ ≤ 1 + r := by linarith
  have hden_ge : 1 - r ≤ ‖(1 : ℂ) - u‖ := by
    have h : ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) - u‖ + ‖u‖ := by
      calc ‖(1 : ℂ)‖ = ‖((1 : ℂ) - u) + u‖ := by rw [sub_add_cancel]
        _ ≤ ‖(1 : ℂ) - u‖ + ‖u‖ := norm_add_le _ _
    rw [norm_one] at h
    linarith
  have hnum_pos : 0 < ‖(1 : ℂ) + u‖ := by linarith
  have hden_pos : 0 < ‖(1 : ℂ) - u‖ := by linarith
  rw [Complex.log_re, norm_div, Real.log_div (ne_of_gt hnum_pos) (ne_of_gt hden_pos),
    Real.log_div (ne_of_gt hr1pos') (ne_of_gt hr1pos), abs_le]
  constructor
  · have h1 : Real.log (1 - r) ≤ Real.log ‖(1 : ℂ) + u‖ := Real.log_le_log hr1pos hnum_ge
    have h2 : Real.log ‖(1 : ℂ) - u‖ ≤ Real.log (1 + r) := Real.log_le_log hden_pos hden_le
    linarith
  · have h1 : Real.log (1 - r) ≤ Real.log ‖(1 : ℂ) - u‖ := Real.log_le_log hr1pos hden_ge
    have h2 : Real.log ‖(1 : ℂ) + u‖ ≤ Real.log (1 + r) := Real.log_le_log hnum_pos hnum_le
    linarith

end Commons.Analysis.Complex