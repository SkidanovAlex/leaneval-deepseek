import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- Subtraction formula for the arctangent, valid when `a * b > -1`. -/
theorem arctan_sub_eq_arctan_div (a b : ℝ) (h : -1 < a * b) :
    Real.arctan a - Real.arctan b = Real.arctan ((a - b) / (1 + a * b)) := by
  have h' : a * (-b) < 1 := by nlinarith
  have hA := Real.arctan_add (x := a) (y := -b) h'
  rw [Real.arctan_neg] at hA
  rw [sub_eq_add_neg, hA]
  congr 1
  rw [show a + -b = a - b by ring, show 1 - a * (-b) = 1 + a * b by ring]

theorem arctan_shift_bound (u v : ℝ) (hu : (1 : ℝ) / 2 ≤ u) (hv : 0 ≤ v) :
    v * (Real.arctan (u / v) - Real.arctan (1 / (2 * v))) ≤
      (2 * u - 1) * v ^ 2 / (2 * v ^ 2 + u) := by
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · rw [← hv0]; simp
  · have hpu : 0 < u := by linarith
    have h2u : 0 ≤ 2 * u - 1 := by linarith
    have hden : 0 < 2 * v ^ 2 + u := by nlinarith [sq_nonneg v]
    set T : ℝ := (2 * u - 1) * v / (2 * v ^ 2 + u) with hT
    have hTnonneg : 0 ≤ T := by
      rw [hT]
      exact div_nonneg (mul_nonneg h2u (le_of_lt hvpos)) (le_of_lt hden)
    have hargpos : -1 < (u / v) * (1 / (2 * v)) := by
      have : 0 < (u / v) * (1 / (2 * v)) := by positivity
      linarith
    have key : Real.arctan (u / v) - Real.arctan (1 / (2 * v)) = Real.arctan T := by
      rw [arctan_sub_eq_arctan_div (u / v) (1 / (2 * v)) hargpos]
      congr 1
      rw [hT]
      have hvne : v ≠ 0 := ne_of_gt hvpos
      have hdenne : 2 * v ^ 2 + u ≠ 0 := ne_of_gt hden
      field_simp
    calc
      v * (Real.arctan (u / v) - Real.arctan (1 / (2 * v)))
          = v * Real.arctan T := by rw [key]
      _ ≤ v * T := mul_le_mul_of_nonneg_left
            (Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg hTnonneg)
            (le_of_lt hvpos)
      _ = (2 * u - 1) * v ^ 2 / (2 * v ^ 2 + u) := by rw [hT]; ring

end Commons.Analysis.SpecialFunctions.Gamma
