import Mathlib
import Submission.Work.CNum.tD_aux

namespace Work.CNum

/-- `u1J m = 24 m rJ^(m-1) uJ / (1 - rJ^m)` with `0 < rJ < 1`.  Bounding
`1 - rJ^m ≥ 1 - rJ` (for `m ≥ 1`) makes `u1J (m+1)` dominated by a constant
multiple of `((m : ℝ) + 1) * rJ^m`, which is summable by the geometric series
and its derivative. -/
theorem u1J_summable : Summable (fun m : ℕ => u1J (m + 1)) := by
  have hr : ‖rJ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos rJ_pos]; exact rJ_lt_one
  have hsum : Summable (fun m : ℕ => ((m : ℝ) + 1) * rJ ^ m) := by
    have h1 : Summable (fun m : ℕ => (m : ℝ) * rJ ^ m) := by
      have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := rJ) hr
      simpa using this
    have h2 : Summable (fun m : ℕ => rJ ^ m) := summable_geometric_of_norm_lt_one hr
    have h3 := h1.add h2
    simpa only [add_mul, one_mul] using h3
  have hle : ∀ m : ℕ, u1J (m + 1) ≤ (24 * uJ / (1 - rJ)) * (((m : ℝ) + 1) * rJ ^ m) := by
    intro m
    set a : ℝ := 24 * ((m : ℝ) + 1) * rJ ^ m * uJ with ha
    have hnum : 0 ≤ a := by
      rw [ha]
      have h1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) (pow_nonneg rJ_nonneg m))
        (le_of_lt uJ_pos)
    have hm1 : 1 ≤ m + 1 := by omega
    have hden_le : 1 - rJ ≤ 1 - rJ ^ (m + 1) := by
      have := rJ_pow_le_rJ hm1; linarith
    have hL : u1J (m + 1) = a / (1 - rJ ^ (m + 1)) := by
      rw [ha, u1J, Nat.add_sub_cancel]; push_cast; ring
    have hR : (24 * uJ / (1 - rJ)) * (((m : ℝ) + 1) * rJ ^ m) = a / (1 - rJ) := by
      rw [ha, div_mul_eq_mul_div]
      congr 1
      ring
    rw [hL, hR]
    exact div_le_div_of_nonneg_left hnum one_sub_rJ_pos hden_le
  refine Summable.of_nonneg_of_le (fun m => u1J_nonneg (m := m + 1) (by omega)) hle ?_
  exact hsum.mul_left (24 * uJ / (1 - rJ))

end Work.CNum
