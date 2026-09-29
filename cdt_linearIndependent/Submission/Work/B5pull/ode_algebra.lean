import Mathlib

namespace Work.B5pull

/-- Algebraic core of the "pullback" step: given the relations among `Y, Th, V, W` and their
derivatives, the two first-order equations for `U'` and `W'` force the explicit expressions
for `V'` and `U'`. -/
theorem ode_algebra {Y Th U W V Y' Th' U' W' V' : ℂ} (hTh : Th ≠ 0) (hY : Y ≠ 0)
    (hTh2 : Th ^ 2 = Y - 4) (hY' : Y' = 2 * Th * Th') (hW : W = 2 * Y + Th * V)
    (hWdiff : W' = 2 * Y' + Th' * V + Th * V')
    (hU' : 2 * Y * (4 - Y) * U' = Y' * ((4 - Y) * U - 2 * W + 4 * Y))
    (hW' : Y * (4 - Y) * W' = Y' * ((2 - Y) * W + Y ^ 2)) :
    V' = (Th * Th' / Y) * V - 2 * Th' ∧ U' = (Y' / (2 * Y)) * U + (2 * Th' / Y) * V := by
  -- `4 - Y = -Th^2 ≠ 0`, so all the coefficients we cancel are nonzero.
  have h4 : (4 : ℂ) - Y = -Th ^ 2 := by linear_combination hTh2
  have h4ne : (4 : ℂ) - Y ≠ 0 := by rw [h4]; exact neg_ne_zero.mpr (pow_ne_zero 2 hTh)
  have hY4ne : Y * (4 - Y) ≠ 0 := mul_ne_zero hY h4ne
  have hcoef : Y * (4 - Y) * Th ≠ 0 := mul_ne_zero hY4ne hTh
  have hcoef2 : 2 * Y * (4 - Y) ≠ 0 := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero h2 hY) h4ne
  constructor
  · -- Substitute `W = 2Y + Th·V` and `W' = 2Y' + Th'V + ThV'` into the `W'`-equation.
    have e : Y * (4 - Y) * (2 * Y' + Th' * V + Th * V')
        = Y' * ((2 - Y) * (2 * Y + Th * V) + Y ^ 2) := by
      rw [← hWdiff, ← hW]; exact hW'
    -- The resulting linear equation for `V'`, after using `Th^2 = Y - 4` and `Y' = 2ThTh'`.
    have hV2 : Y * (4 - Y) * Th * V'
        = (4 - Y) * Th ^ 2 * Th' * V - 2 * Y * (4 - Y) * Th * Th' := by
      linear_combination e + (-Y * (4 - Y) + (2 - Y) * Th * V) * hY' + (-Y * Th' * V) * hTh2
    have hstep : (4 - Y) * Th ^ 2 * Th' * V - 2 * Y * (4 - Y) * Th * Th'
        = Y * (4 - Y) * Th * ((Th * Th' / Y) * V - 2 * Th') := by
      field_simp
    rw [hstep] at hV2
    exact mul_left_cancel₀ hcoef hV2
  · -- Substitute `W = 2Y + Th·V` into the `U'`-equation.
    have f : 2 * Y * (4 - Y) * U' = Y' * ((4 - Y) * U - 2 * Th * V) := by
      rw [hW] at hU'
      linear_combination hU'
    have hU2 : 2 * Y * (4 - Y) * U' = (4 - Y) * Y' * U + 4 * (4 - Y) * Th' * V := by
      linear_combination f - (4 * Th' * V) * hTh2 - (2 * Th * V) * hY'
    have hstep2 : (4 - Y) * Y' * U + 4 * (4 - Y) * Th' * V
        = 2 * Y * (4 - Y) * ((Y' / (2 * Y)) * U + (2 * Th' / Y) * V) := by
      field_simp
      ring
    rw [hstep2] at hU2
    exact mul_left_cancel₀ hcoef2 hU2

end Work.B5pull
