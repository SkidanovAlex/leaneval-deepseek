import Mathlib
import Submission.Work.HP.Q44Main.q44_geom_quarter
import Submission.Work.HP.Q44Main.q44_stepB

namespace Work.HP.Q44Main

/-- Key exponential estimate: for `a + b + c ≤ N` we have
`2^(a + b + 3c) ≤ 2^(3N) · (1/4)^(a+b)`.  Indeed `a + b + 3c = 3(a+b+c) - 2(a+b)`,
so `3(a+b+c) ≤ 3N` gives the claim after clearing the positive factor `4^(a+b)`. -/
lemma q44_pow_key (a b c N : ℕ) (h : a + b + c ≤ N) :
    (2 : ℝ) ^ (a + b + 3 * c) ≤ (2 : ℝ) ^ (3 * N) * ((1 : ℝ) / 4) ^ (a + b) := by
  have h3 : (2 : ℝ) ^ (a + b + 3 * c) * (4 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ (3 * N) := by
    rw [show (2 : ℝ) ^ (a + b + 3 * c) * (4 : ℝ) ^ (a + b)
          = (2 : ℝ) ^ (3 * (a + b + c)) by
      rw [show (4 : ℝ) ^ (a + b) = (2 : ℝ) ^ (2 * (a + b)) by rw [pow_mul]; norm_num]
      rw [← pow_add]
      congr 1
      omega]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hpos : (0 : ℝ) < (4 : ℝ) ^ (a + b) := by positivity
  have h4 : (2 : ℝ) ^ (a + b + 3 * c) ≤ (2 : ℝ) ^ (3 * N) / (4 : ℝ) ^ (a + b) :=
    (le_div_iff₀ hpos).mpr h3
  calc (2 : ℝ) ^ (a + b + 3 * c) ≤ (2 : ℝ) ^ (3 * N) / (4 : ℝ) ^ (a + b) := h4
    _ = (2 : ℝ) ^ (3 * N) * ((1 : ℝ) / 4) ^ (a + b) := by
        rw [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num, inv_pow, div_eq_mul_inv]

theorem q44_S2_bound (N : ℕ) :
    (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
      (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N then (2 : ℝ) ^ (a + b + 3 * c) else 0))
    ≤ 2 * ((N : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (3 * N) := by
  -- Step 1: drop the shape constraint `a ≤ b ≤ c`; the term only grows.
  have hstep1 :
      (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
        (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N then (2 : ℝ) ^ (a + b + 3 * c) else 0))
      ≤ (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
        (if a + b + c ≤ N then (2 : ℝ) ^ (a + b + 3 * c) else 0)) := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    apply Finset.sum_le_sum; intro c _
    by_cases h : a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N
    · simp [h]
    · rw [ite_eq_right h]
      by_cases h2 : a + b + c ≤ N
      · rw [ite_eq_left h2]; positivity
      · rw [ite_eq_right h2]
  -- Step 2: extract the factor `2^(3N)` using the pointwise estimate `q44_pow_key`.
  have hstep2 :
      (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
        (if a + b + c ≤ N then (2 : ℝ) ^ (a + b + 3 * c) else 0))
      ≤ (2 : ℝ) ^ (3 * N) *
        (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
          (if a + b + c ≤ N then ((1 : ℝ) / 4) ^ (a + b) else 0)) := by
    have hpt : ∀ a b c : ℕ, (if a + b + c ≤ N then (2 : ℝ) ^ (a + b + 3 * c) else 0)
        ≤ (2 : ℝ) ^ (3 * N) * (if a + b + c ≤ N then ((1 : ℝ) / 4) ^ (a + b) else 0) := by
      intro a b c
      by_cases h : a + b + c ≤ N
      · rw [ite_eq_left h, ite_eq_left h]
        exact q44_pow_key a b c N h
      · rw [ite_eq_right h, ite_eq_right h, mul_zero]
    calc (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
          (if a + b + c ≤ N then (2 : ℝ) ^ (a + b + 3 * c) else 0))
        ≤ ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
            (2 : ℝ) ^ (3 * N) *
              (if a + b + c ≤ N then ((1 : ℝ) / 4) ^ (a + b) else 0) := by
          apply Finset.sum_le_sum; intro a _
          apply Finset.sum_le_sum; intro b _
          apply Finset.sum_le_sum; intro c _
          exact hpt a b c
      _ = (2 : ℝ) ^ (3 * N) *
          (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
            (if a + b + c ≤ N then ((1 : ℝ) / 4) ^ (a + b) else 0)) := by
          simp only [← Finset.mul_sum]
  calc
    (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
      (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N then (2 : ℝ) ^ (a + b + 3 * c) else 0))
      ≤ (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
        (if a + b + c ≤ N then (2 : ℝ) ^ (a + b + 3 * c) else 0)) := hstep1
    _ ≤ (2 : ℝ) ^ (3 * N) *
        (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
          (if a + b + c ≤ N then ((1 : ℝ) / 4) ^ (a + b) else 0)) := hstep2
    _ ≤ (2 : ℝ) ^ (3 * N) * (2 * ((N : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left (q44_stepB N) (by positivity)
    _ ≤ 2 * ((N : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (3 * N) := by
        have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
          have h0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          linarith
        have h0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by linarith
        have hy : ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ 2 := by
          rw [pow_two]
          exact le_mul_of_one_le_left h0 h1
        have hC : (0 : ℝ) < (2 : ℝ) ^ (3 * N) := by positivity
        calc (2 : ℝ) ^ (3 * N) * (2 * ((N : ℝ) + 1))
            = 2 * ((N : ℝ) + 1) * (2 : ℝ) ^ (3 * N) := by ring
          _ ≤ 2 * ((N : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (3 * N) := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hC)
              linarith [hy]

end Work.HP.Q44Main
