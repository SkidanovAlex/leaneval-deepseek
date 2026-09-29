import Mathlib

namespace Work.C17I

/-- Auxiliary summability fact: for `0 < r < 1` and `k : ℕ`, the series
`∑ (n+1)^k r^n` converges.  Obtained from Mathlib's
`summable_pow_mul_geometric_of_norm_lt_one` by shifting the index and dividing
by the (nonzero) ratio. -/
theorem summable_pow_add_one_mul_geometric {k : ℕ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ n) := by
  have ha : Summable (fun m : ℕ => (m : ℝ) ^ k * r ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
  have hshift : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ (n + 1)) := by
    have h := (summable_nat_add_iff 1).mpr ha
    simpa [Nat.cast_add, Nat.cast_one] using h
  have h2 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ k * r ^ n) * r) := by
    simpa only [pow_succ, mul_assoc] using hshift
  have h3 : Summable (fun n : ℕ => ((((n : ℝ) + 1) ^ k * r ^ n) * r) / r) := h2.div_const r
  refine h3.congr (fun n => ?_)
  rw [mul_div_cancel_right₀ _ (ne_of_gt hr0)]

theorem hasSum_tsum_of_poly_growth {c : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C) {k : ℕ}
    (hc : ∀ n : ℕ, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ k) :
    ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n : ℕ => c n * z ^ n) (∑' n : ℕ, c n * z ^ n) := by
  intro z hz
  let r : ℝ := ‖z‖
  have hr1 : r < 1 := hz
  -- enlarge the ratio to a positive one so that we can divide by it
  let r' : ℝ := max r (1 / 2)
  have hr'0 : 0 < r' := lt_of_lt_of_le (by norm_num) (le_max_right r (1 / 2))
  have hr'1 : r' < 1 := max_lt hr1 (by norm_num)
  have hr0 : 0 ≤ r := norm_nonneg z
  have hrr' : r ≤ r' := le_max_left r (1 / 2)
  -- summability of the comparison series
  have hb : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * r' ^ n) :=
    summable_pow_add_one_mul_geometric hr'0 hr'1
  have hg : Summable (fun n : ℕ => C * (((n : ℝ) + 1) ^ k * r' ^ n)) := hb.mul_left C
  -- termwise bound
  have hbound : ∀ n : ℕ, ‖c n * z ^ n‖ ≤ C * (((n : ℝ) + 1) ^ k * r' ^ n) := by
    intro n
    have hzpow : ‖z ^ n‖ = r ^ n := by rw [norm_pow]
    rw [norm_mul, hzpow]
    calc ‖c n‖ * r ^ n ≤ (C * ((n : ℝ) + 1) ^ k) * r ^ n :=
          mul_le_mul_of_nonneg_right (hc n) (pow_nonneg hr0 n)
      _ ≤ (C * ((n : ℝ) + 1) ^ k) * r' ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrr' n) (by positivity)
      _ = C * (((n : ℝ) + 1) ^ k * r' ^ n) := by ring
  exact (Summable.of_norm_bounded hg hbound).hasSum

end Work.C17I
