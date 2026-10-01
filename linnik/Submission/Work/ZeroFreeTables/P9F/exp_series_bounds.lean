import Mathlib

namespace Work.ZeroFreeTables.P9F

theorem exp_series_bounds (n : ℕ) (hn : 0 < n) :
    ∀ w : ℝ, 0 ≤ w → w < n →
      (∑ k ∈ Finset.range n, w ^ k / (k.factorial : ℝ)) ≤ Real.exp w ∧
      Real.exp w ≤ (∑ k ∈ Finset.range n, w ^ k / (k.factorial : ℝ))
        + w ^ n / (n.factorial : ℝ) * (1 / (1 - w / n)) := by
  intro w hw0 hwn
  refine ⟨Real.sum_le_exp_of_nonneg hw0 n, ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : 0 ≤ w / n := div_nonneg hw0 hnR.le
  have hr1 : w / n < 1 := by
    rw [div_lt_one hnR]; exact_mod_cast hwn
  have hsummable : Summable (fun k : ℕ => w ^ k / (k.factorial : ℝ)) :=
    Real.summable_pow_div_factorial w
  have hsplit : (∑ i ∈ Finset.range n, w ^ i / (i.factorial : ℝ))
      + ∑' i : ℕ, w ^ (i + n) / ((i + n).factorial : ℝ)
      = ∑' i : ℕ, w ^ i / (i.factorial : ℝ) := hsummable.sum_add_tsum_nat_add n
  have hexp : Real.exp w = ∑' k : ℕ, w ^ k / (k.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hfact : ∀ j : ℕ, n.factorial * n ^ j ≤ (n + j).factorial := by
    intro j
    calc n.factorial * n ^ j ≤ n.factorial * (n + 1) ^ j := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_left (Nat.le_succ n) j
      _ ≤ (n + j).factorial := Nat.factorial_mul_pow_le_factorial (m := n) (n := j)
  have hpoint : ∀ j : ℕ, w ^ (j + n) / ((j + n).factorial : ℝ) ≤
      (w ^ n / (n.factorial : ℝ)) * (w / n) ^ j := by
    intro j
    have hcast : (n.factorial : ℝ) * (n : ℝ) ^ j ≤ ((n + j).factorial : ℝ) := by
      exact_mod_cast hfact j
    have hden : (0 : ℝ) < (n.factorial : ℝ) * (n : ℝ) ^ j := by positivity
    have hstep : w ^ (j + n) / ((j + n).factorial : ℝ) ≤
        w ^ (j + n) / ((n.factorial : ℝ) * (n : ℝ) ^ j) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact hden
      · have hjn : ((j + n).factorial : ℝ) = ((n + j).factorial : ℝ) := by
          rw [Nat.add_comm]
        rw [hjn]; exact hcast
    have heq : w ^ (j + n) / ((n.factorial : ℝ) * (n : ℝ) ^ j) =
        (w ^ n / (n.factorial : ℝ)) * (w / n) ^ j := by
      rw [div_pow, pow_add]
      field_simp
    exact hstep.trans heq.le
  have htail_sum : Summable (fun j : ℕ => w ^ (j + n) / ((j + n).factorial : ℝ)) := by
    have := (summable_nat_add_iff n).2 hsummable
    simpa [add_comm] using this
  have hgeom_sum : Summable (fun j : ℕ => (w ^ n / (n.factorial : ℝ)) * (w / n) ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have htail_le : ∑' j : ℕ, w ^ (j + n) / ((j + n).factorial : ℝ) ≤
      ∑' j : ℕ, (w ^ n / (n.factorial : ℝ)) * (w / n) ^ j :=
    Summable.tsum_le_tsum hpoint htail_sum hgeom_sum
  have hgeom_val : ∑' j : ℕ, (w ^ n / (n.factorial : ℝ)) * (w / n) ^ j =
      (w ^ n / (n.factorial : ℝ)) * (1 - w / n)⁻¹ := by
    rw [Summable.tsum_mul_left (w ^ n / (n.factorial : ℝ))
        (summable_geometric_of_lt_one hr0 hr1),
      tsum_geometric_of_lt_one hr0 hr1]
  calc Real.exp w = ∑' k : ℕ, w ^ k / (k.factorial : ℝ) := hexp
    _ = (∑ i ∈ Finset.range n, w ^ i / (i.factorial : ℝ))
          + ∑' i : ℕ, w ^ (i + n) / ((i + n).factorial : ℝ) := hsplit.symm
    _ ≤ (∑ i ∈ Finset.range n, w ^ i / (i.factorial : ℝ))
          + (w ^ n / (n.factorial : ℝ)) * (1 - w / n)⁻¹ :=
        add_le_add_right (hgeom_val ▸ htail_le) _
    _ = (∑ k ∈ Finset.range n, w ^ k / (k.factorial : ℝ))
          + w ^ n / (n.factorial : ℝ) * (1 / (1 - w / n)) := by rw [inv_eq_one_div]

end Work.ZeroFreeTables.P9F
