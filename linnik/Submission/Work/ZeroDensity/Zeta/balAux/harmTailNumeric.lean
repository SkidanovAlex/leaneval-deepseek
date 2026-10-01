import Mathlib

namespace Work.ZeroDensity.Zeta.balAux

/-- Numerical bound: for `y ≥ 3`, with `n = ⌊y⌋₊` the `n`-th harmonic number
satisfies `2 H_n / n ≤ 16 (log y + 1) / y`.

The estimate follows from Mathlib's `H_n ≤ 1 + log n ≤ 1 + log y` together with
the crude bound `y < n + 1 ≤ 8n` (valid since `n ≥ 1`). -/
theorem harmTailNumeric (y : ℝ) (hy : 3 ≤ y) :
    2 * (harmonic ⌊y⌋₊ : ℝ) / (⌊y⌋₊ : ℝ) ≤ 16 * (Real.log y + 1) / y := by
  have hy1 : (1:ℝ) ≤ y := by linarith
  have hypos : (0:ℝ) < y := by linarith
  have hfloor3 : 3 ≤ ⌊y⌋₊ := Nat.le_floor (show (3:ℝ) ≤ y from hy)
  have hnpos_nat : 0 < ⌊y⌋₊ := by omega
  have hnpos : (0:ℝ) < (⌊y⌋₊ : ℝ) := by exact_mod_cast hnpos_nat
  have hH : (harmonic ⌊y⌋₊ : ℝ) ≤ 1 + Real.log y := harmonic_floor_le_one_add_log y hy1
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hylt : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have h8 : y ≤ 8 * (⌊y⌋₊ : ℝ) := by
    have h3 : (3:ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hfloor3
    linarith
  have hstep1 : 2 * (harmonic ⌊y⌋₊ : ℝ) / (⌊y⌋₊ : ℝ) ≤ 2 * (1 + Real.log y) / (⌊y⌋₊ : ℝ) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hnpos)
    linarith
  have hstep2 : 2 * (1 + Real.log y) / (⌊y⌋₊ : ℝ) ≤ 16 * (Real.log y + 1) / y := by
    rw [div_le_div_iff₀ hnpos hypos]
    nlinarith [h8, hlog]
  linarith

end Work.ZeroDensity.Zeta.balAux
