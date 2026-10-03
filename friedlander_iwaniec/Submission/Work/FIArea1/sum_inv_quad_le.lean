import Mathlib

namespace Work.FIArea1

open scoped BigOperators

/-- For `2 ≤ n`, the reciprocal square is bounded by the telescoping difference
`1/(n-1) - 1/n`. -/
lemma sq_inv_le (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ))⁻¹ ^ 2 ≤ ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hn1' : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  rw [inv_sub_inv hn1'.ne' hn0.ne']
  rw [show ((n : ℝ) - ((n : ℝ) - 1)) = 1 by ring, one_div, inv_pow]
  rw [mul_comm]
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  nlinarith

/-- Tail bound: `∑_{n=m+1}^{N} 1/n² ≤ 1/m`. -/
lemma sum_Icc_sq_inv_le (m N : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Icc (m + 1) N, ((n : ℝ))⁻¹ ^ 2 ≤ (m : ℝ)⁻¹ := by
  by_cases h : m + 1 ≤ N
  · have key : ∑ n ∈ Finset.Icc (m + 1) N, ((n : ℝ))⁻¹ ^ 2 ≤
        ∑ n ∈ Finset.Icc (m + 1) N, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Finset.mem_Icc] at hn
      exact sq_inv_le n (by omega)
    have tel : ∑ n ∈ Finset.Icc (m + 1) N, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) =
        (m : ℝ)⁻¹ - (N : ℝ)⁻¹ := by
      rw [← Finset.Ico_succ_right_eq_Icc (m + 1) N, Order.succ_eq_add_one,
        Finset.sum_Ico_eq_sum_range]
      rw [show (N + 1) - (m + 1) = N - m by omega]
      have hc : ∀ k : ℕ, ((((m + 1) + k : ℕ) : ℝ) - 1)⁻¹ - ((((m + 1) + k : ℕ) : ℝ))⁻¹
          = ((m + k : ℕ) : ℝ)⁻¹ - ((m + k + 1 : ℕ) : ℝ)⁻¹ := by
        intro k; congr 2 <;> push_cast <;> ring
      simp only [hc]
      simp only [Nat.add_assoc]
      rw [Finset.sum_range_sub']
      simp only [Nat.add_zero]
      rw [show m + (N - m) = N by omega]
    calc _ ≤ _ := key
       _ = (m : ℝ)⁻¹ - (N : ℝ)⁻¹ := tel
       _ ≤ (m : ℝ)⁻¹ := by
            have : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
            linarith
  · rw [Finset.Icc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity

/-- Inner bound: `∑_{n=1}^{N} 1/(m²+n²) ≤ 2/m` for `1 ≤ m ≤ N`. -/
lemma inner_le (m N : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹ ≤ 2 * (m : ℝ)⁻¹ := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hA : ∑ n ∈ Finset.Ico 1 (m + 1), ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹ ≤ (m : ℝ)⁻¹ := by
    calc ∑ n ∈ Finset.Ico 1 (m + 1), ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹
        ≤ ∑ n ∈ Finset.Ico 1 (m + 1), ((m : ℝ)⁻¹) ^ 2 := by
          apply Finset.sum_le_sum
          intro n _
          have h1 : (0 : ℝ) < (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by positivity
          have h2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
          rw [inv_pow]
          exact (inv_le_inv₀ h1 h2).2 (by nlinarith [sq_nonneg (n : ℝ)])
      _ = (m : ℝ)⁻¹ := by
          rw [Finset.sum_const, Nat.card_Ico]
          rw [show m + 1 - 1 = m by omega]
          simp only [nsmul_eq_mul]
          rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hm0.ne', one_mul]
  have hB : ∑ n ∈ Finset.Ico (m + 1) (N + 1), ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹ ≤ (m : ℝ)⁻¹ := by
    rw [show N + 1 = Order.succ N by rw [Order.succ_eq_add_one]]
    rw [Finset.Ico_succ_right_eq_Icc (m + 1) N]
    calc ∑ n ∈ Finset.Icc (m + 1) N, ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹
        ≤ ∑ n ∈ Finset.Icc (m + 1) N, ((n : ℝ)⁻¹) ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Icc] at hn
          have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
          have h1 : (0 : ℝ) < (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by positivity
          rw [inv_pow]
          exact (inv_le_inv₀ h1 (by positivity)).2 (by nlinarith [sq_nonneg (m : ℝ)])
      _ ≤ (m : ℝ)⁻¹ := sum_Icc_sq_inv_le m N hm1
  rw [← Finset.Ico_succ_right_eq_Icc (1 : ℕ) N, Order.succ_eq_add_one]
  rw [← Finset.sum_Ico_consecutive (fun n => ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹)
    (by omega : (1 : ℕ) ≤ m + 1) (by omega : m + 1 ≤ N + 1)]
  linarith

/-- The harmonic sum is bounded by `1 + log N`. -/
lemma sum_Icc_inv_le_log (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, ((m : ℝ))⁻¹ ≤ 1 + Real.log (N : ℝ) := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa using h

theorem sum_inv_quad_le (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (((m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹)) ≤ 2 * (1 + Real.log (N : ℝ)) := by
  have hmain : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹ ≤ 2 * ∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_Icc] at hm
    exact inner_le m N hm.1 hm.2
  have hlog := sum_Icc_inv_le_log N
  calc ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹
      ≤ 2 * ∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹ := hmain
    _ ≤ 2 * (1 + Real.log (N : ℝ)) := by linarith

end Work.FIArea1
