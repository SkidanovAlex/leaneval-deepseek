import Mathlib

namespace Work.HP.NA

set_option linter.unusedVariables false in
/-- Arithmetic inequality: with `X, Y ≤ p^{-5/4}` (and `X, Y ∈ [0,1]`), the "union measure"
`1 - (1-X)(1-Y) = X + Y - XY` is at most `2 p^{-5/4}`, so `κ · (1 - (1-X)(1-Y)) ≤ p^{-5/4}`
whenever `κ ≤ 1/12`.  Multiplying by `M ≥ 0` gives the claimed bound. -/
theorem gt_arith (p M κ X Y : ℝ) (hp : 2 ≤ p) (hM : 0 ≤ M) (hκ : κ ≤ 1/12)
    (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1)
    (hX : X ≤ 1 / p ^ ((5:ℝ)/4)) (hY : Y ≤ 1 / p ^ ((5:ℝ)/4)) :
    (1 + κ) * M - κ * (M * ((1 - X) * (1 - Y))) ≤ M * (1 + 1 / p ^ ((5:ℝ)/4)) := by
  set c := 1 / p ^ ((5:ℝ)/4) with hcdef
  have hp0 : 0 < p := by linarith
  have hc0 : 0 < c := by
    rw [hcdef]
    exact div_pos one_pos (Real.rpow_pos_of_pos hp0 _)
  have hc0' : 0 ≤ c := le_of_lt hc0
  have hXc : X ≤ c := by rw [hcdef]; exact hX
  have hYc : Y ≤ c := by rw [hcdef]; exact hY
  have hd0 : 0 ≤ 1 - (1 - X) * (1 - Y) := by nlinarith [hX0, hX1, hY0, hY1]
  have hdle : 1 - (1 - X) * (1 - Y) ≤ X + Y := by nlinarith [mul_nonneg hX0 hY0]
  have hXY : X + Y ≤ 2 * c := by linarith
  have hkd : κ * (1 - (1 - X) * (1 - Y)) ≤ c := by
    have h1 : κ * (1 - (1 - X) * (1 - Y)) ≤ (1/12) * (1 - (1 - X) * (1 - Y)) :=
      mul_le_mul_of_nonneg_right hκ hd0
    have h2 : (1/12) * (1 - (1 - X) * (1 - Y)) ≤ (1/12) * (2 * c) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    have h3 : (1/12) * (2 * c) ≤ c := by linarith
    linarith [h1, h2, h3]
  have hmain : M * (κ * (1 - (1 - X) * (1 - Y)) - c) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hM (by linarith)
  have : (1 + κ) * M - κ * (M * ((1 - X) * (1 - Y))) - M * (1 + c) ≤ 0 := by
    nlinarith [hmain]
  linarith [this]

end Work.HP.NA
