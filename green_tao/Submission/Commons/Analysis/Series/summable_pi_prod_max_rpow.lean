import Mathlib.Analysis.PSeries
import Submission.Commons.Analysis.TSum.summable_pi_prod

namespace Commons.Analysis.Series

/-- The one-variable `p`-series with base `max j 1` is summable as soon as the
exponent `-c` is strictly below `-1`, i.e. `1 < c`. -/
theorem summable_max_one_rpow_neg {c : ℝ} (hc : 1 < c) :
    Summable (fun j : ℕ => (max (j : ℝ) 1) ^ (-c)) := by
  rw [← summable_nat_add_iff 1]
  have h : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-c)) := by
    have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (-c)) := by
      rw [Real.summable_nat_rpow]
      linarith
    have h1 := (summable_nat_add_iff 1).mpr h0
    simpa [Nat.cast_add, Nat.cast_one] using h1
  refine h.congr ?_
  intro n
  have hle : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [Nat.cast_add, Nat.cast_one, max_eq_left hle]

theorem summable_pi_prod_max_rpow {m : ℕ} {c : ℝ} (hc : (m : ℝ) < c) :
    Summable (fun d : Fin m → ℕ => ∏ i, (max (d i : ℝ) 1) ^ (-c)) := by
  classical
  refine Commons.Analysis.TSum.summable_pi_prod_nonneg
    (f := fun (_ : Fin m) (j : ℕ) => (max (j : ℝ) 1) ^ (-c)) ?_ ?_
  · intro i j
    positivity
  · intro i
    have hm1 : 1 ≤ m := by
      have := i.isLt
      omega
    have hc1 : (1 : ℝ) < c := by
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      linarith
    exact summable_max_one_rpow_neg hc1

end Commons.Analysis.Series