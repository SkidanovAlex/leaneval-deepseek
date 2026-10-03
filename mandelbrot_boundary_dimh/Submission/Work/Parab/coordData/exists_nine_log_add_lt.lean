import Mathlib

namespace Work.Parab.coordData

/-- Elementary quadratic estimate: once `y` dominates `18 K + B + 1`, the linear expression
`18 K y + B` is strictly below `y ^ 2` (for `K, B ≥ 0`). -/
private lemma nine_log_aux (K B y : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hy : 18 * K + B + 1 ≤ y) : 18 * K * y + B < y ^ 2 := by
  nlinarith [hy, hK, hB]

/-- `Real.log` is `o(x)`: for constants `K, D ≥ 0` there is a threshold `N` beyond which
`9 * (K * (Real.log x + Real.pi) + D) < x`. -/
theorem exists_nine_log_add_lt (K D : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D) :
    ∃ N : ℝ, ∀ x : ℝ, N ≤ x → 9 * (K * (Real.log x + Real.pi) + D) < x := by
  -- `B` collects the constant part of the left-hand side
  set B : ℝ := 9 * (K * Real.pi + D) with hBdef
  have hB : 0 ≤ B := by
    rw [hBdef]
    have : 0 ≤ K * Real.pi := mul_nonneg hK Real.pi_pos.le
    linarith
  -- the threshold is essentially `Y ^ 2`, so that `Real.sqrt x ≥ Y`
  set Y : ℝ := 18 * K + B + 1 with hYdef
  have hY1 : 1 ≤ Y := by rw [hYdef]; linarith
  have hY0 : 0 ≤ Y := le_trans zero_le_one hY1
  refine ⟨Y ^ 2, fun x hx => ?_⟩
  have hxY : Y ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    rwa [Real.sqrt_sq hY0] at h
  have hx1 : 1 ≤ x := by
    have hyy : Y ≤ Y ^ 2 := by nlinarith [hY1]
    linarith
  -- `log x ≤ 2 √x` for `x ≥ 1`
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have h := Real.log_le_rpow_div (le_trans zero_le_one hx1) (by norm_num : (0:ℝ) < 1/2)
    rw [show x ^ ((1:ℝ)/2) / ((1:ℝ)/2) = 2 * Real.sqrt x by rw [Real.sqrt_eq_rpow]; ring] at h
    exact h
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_trans zero_le_one hx1)
  have h9 : 9 * (K * (Real.log x + Real.pi) + D) = 9 * K * Real.log x + B := by
    rw [hBdef]; ring
  have key : 9 * (K * (Real.log x + Real.pi) + D) ≤ 18 * K * Real.sqrt x + B := by
    rw [h9]
    have hm : 9 * K * Real.log x ≤ 9 * K * (2 * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left hlog (by nlinarith [hK])
    have he : 9 * K * (2 * Real.sqrt x) = 18 * K * Real.sqrt x := by ring
    linarith [he]
  have hlt : 18 * K * Real.sqrt x + B < Real.sqrt x ^ 2 :=
    nine_log_aux K B (Real.sqrt x) hK hB (by rw [← hYdef]; exact hxY)
  linarith [key, hlt, hsq]

end Work.Parab.coordData
