import Mathlib

namespace Work.ZeroDensity.Jutila

/-- Auxiliary arithmetic inequality used in the Jutila zero-density argument.

For integers `2 ≤ q` and `1 ≤ N ≤ q`, a real `T ≥ 1` and `0 < l ≤ 1`, the
expression `5 * l * (1/l + (1/2) log N + (1/2) log (2 + T) + 4)` is bounded by
`30 * (l * log (q * (T+1)) + 1)`.

The proof compares the three logarithmic terms with `log (q * (T+1))`: this
dominates `log N` (since `N ≤ q ≤ q (T+1)`) and `log (T+1)` (since
`q ≥ 1`), while `log (2+T) ≤ log (T+1) + log 2 ≤ log (T+1) + 1`. -/
theorem linnikDensityAuxArith {q N : ℕ} {l T : ℝ} (hq : 2 ≤ q) (hN1 : 1 ≤ N) (hNq : N ≤ q)
    (hT : 1 ≤ T) (hl0 : 0 < l) (hl1 : l ≤ 1) :
    5 * l * (1 / l + (1 / 2) * Real.log (N : ℝ) + (1 / 2) * Real.log (2 + T) + 4)
      ≤ 30 * (l * Real.log ((q : ℝ) * (T + 1)) + 1) := by
  have hl_nn : (0 : ℝ) ≤ l := le_of_lt hl0
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNq' : (N : ℝ) ≤ (q : ℝ) := by exact_mod_cast hNq
  have hT1 : (1 : ℝ) ≤ T + 1 := by linarith
  have hN_gt : (0 : ℝ) < (N : ℝ) := by linarith
  have hqT_ge1 : (1 : ℝ) ≤ (q : ℝ) * (T + 1) := by nlinarith
  -- `log (q * (T+1))` dominates `log N`
  have hlogN : Real.log (N : ℝ) ≤ Real.log ((q : ℝ) * (T + 1)) := by
    apply Real.log_le_log hN_gt
    nlinarith
  -- and dominates `log (T+1)`
  have hlogT1 : Real.log (T + 1) ≤ Real.log ((q : ℝ) * (T + 1)) := by
    apply Real.log_le_log (by linarith : (0 : ℝ) < T + 1)
    nlinarith
  -- while `log (2+T) ≤ log (T+1) + 1`
  have hlogT2 : Real.log (2 + T) ≤ Real.log (T + 1) + 1 := by
    have hle : 2 + T ≤ 2 * (T + 1) := by linarith
    have h := Real.log_le_log (by linarith : (0 : ℝ) < 2 + T) hle
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : T + 1 ≠ 0)] at h
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  set A : ℝ := l * Real.log ((q : ℝ) * (T + 1)) with hA
  have hA_nn : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg hl_nn (Real.log_nonneg hqT_ge1)
  have hlN_le : l * Real.log (N : ℝ) ≤ A := by
    rw [hA]
    exact mul_le_mul_of_nonneg_left hlogN hl_nn
  have hlT1_le : l * Real.log (T + 1) ≤ A := by
    rw [hA]
    exact mul_le_mul_of_nonneg_left hlogT1 hl_nn
  have hlT2_le : l * Real.log (2 + T) ≤ A + l := by
    have h1 : l * Real.log (2 + T) ≤ l * (Real.log (T + 1) + 1) :=
      mul_le_mul_of_nonneg_left hlogT2 hl_nn
    nlinarith
  have hdecomp : 5 * l * (1 / l + (1 / 2) * Real.log (N : ℝ)
        + (1 / 2) * Real.log (2 + T) + 4)
      = 5 + (5 / 2) * (l * Real.log (N : ℝ)) + (5 / 2) * (l * Real.log (2 + T))
        + 20 * l := by
    field_simp
    ring
  have hmain : 5 * l * (1 / l + (1 / 2) * Real.log (N : ℝ)
        + (1 / 2) * Real.log (2 + T) + 4)
      ≤ 5 + 5 * A + 22.5 * l := by
    rw [hdecomp]
    nlinarith [hlN_le, hlT2_le]
  have hfin : 5 + 5 * A + 22.5 * l ≤ 30 * (A + 1) := by nlinarith [hA_nn, hl1]
  have h3 := le_trans hmain hfin
  simpa [hA] using h3

end Work.ZeroDensity.Jutila
