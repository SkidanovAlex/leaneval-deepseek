import Mathlib

namespace Work.EQ

/-- Telescoping identity for the weighted geometric sum: multiplying
`B_m = ∑_{j<m} (j+1) x^j` by `(1-x)` yields `(∑_{j<m} x^j) - m x^m`. -/
private lemma geom_weighted_telescope (x : ℝ) (m : ℕ) :
    (1 - x) * (∑ j ∈ Finset.range m, ((j : ℝ) + 1) * x^j)
      = (∑ j ∈ Finset.range m, x^j) - (m : ℝ) * x^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih, pow_succ]
    push_cast
    ring

/-- Closed form for the weighted geometric sum:
`(1-x)^2 * ∑_{j<m} (j+1) x^j = 1 - (m+1) x^m + m x^{m+1}`. -/
private lemma geom_weighted_identity (x : ℝ) (m : ℕ) :
    (1 - x)^2 * (∑ j ∈ Finset.range m, ((j : ℝ) + 1) * x^j)
      = 1 - ((m : ℝ) + 1) * x^m + (m : ℝ) * x^(m+1) := by
  rw [pow_two, mul_assoc, geom_weighted_telescope x m, mul_sub, mul_neg_geom_sum, pow_succ]
  ring

/-- Reindexing: `∑_{k < m+1} k κ^{2k-1} = κ * ∑_{j<m} (j+1) (κ^2)^j`. -/
private lemma geom_weighted_reindex (κ : ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (m+1), (k:ℝ) * κ^(2*k-1)
      = κ * (∑ j ∈ Finset.range m, ((j:ℝ)+1) * (κ^2)^j) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h1 : 2*(k+1)-1 = 2*k+1 := by omega
  rw [h1, pow_succ, pow_mul]
  push_cast
  ring

/-- The weighted geometric sum is bounded by `1/(1-x)^2` for `x ∈ [0,1]`. -/
private lemma geom_weighted_bound (x : ℝ) (m : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - x)^2 * (∑ j ∈ Finset.range m, ((j : ℝ) + 1) * x^j) ≤ 1 := by
  rw [geom_weighted_identity x m]
  have key : (m : ℝ) * x^(m+1) ≤ ((m : ℝ) + 1) * x^m := by
    have hxm : 0 ≤ x^m := pow_nonneg hx0 m
    calc (m:ℝ) * x^(m+1) = (m:ℝ) * x^m * x := by rw [pow_succ]; ring
      _ ≤ (m:ℝ) * x^m * 1 := by
            apply mul_le_mul_of_nonneg_left hx1
            exact mul_nonneg (Nat.cast_nonneg m) hxm
      _ = (m:ℝ) * x^m := by ring
      _ ≤ ((m:ℝ)+1) * x^m := by
            apply mul_le_mul_of_nonneg_right _ hxm
            linarith
  linarith

theorem geom_sum_kw_sharp {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, (k : ℝ) * κ ^ (2 * k - 1) ≤ κ / (1 - κ ^ 2) ^ 2 := by
  have hx0 : 0 ≤ κ^2 := sq_nonneg κ
  have hx1' : κ^2 < 1 := by nlinarith [h0, h1]
  have hx1 : κ^2 ≤ 1 := le_of_lt hx1'
  have hpos : 0 < 1 - κ^2 := by linarith
  have hpos2 : 0 < (1 - κ^2)^2 := pow_pos hpos 2
  rw [le_div_iff₀ hpos2]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Finset.sum_range_zero, zero_mul]
    exact h0
  · have hT : (∑ k ∈ Finset.range n, (k : ℝ) * κ ^ (2 * k - 1))
        = κ * (∑ j ∈ Finset.range (n-1), ((j:ℝ)+1) * (κ^2)^j) := by
      have hh := geom_weighted_reindex κ (n-1)
      rwa [Nat.sub_add_cancel hn] at hh
    rw [hT]
    calc (κ * (∑ j ∈ Finset.range (n-1), ((j:ℝ)+1) * (κ^2)^j)) * (1 - κ^2)^2
        = κ * ((1 - κ^2)^2 * (∑ j ∈ Finset.range (n-1), ((j:ℝ)+1) * (κ^2)^j)) := by ring
      _ ≤ κ * 1 := by
            apply mul_le_mul_of_nonneg_left _ h0
            exact geom_weighted_bound (κ^2) (n-1) hx0 hx1
      _ = κ := by ring

end Work.EQ
