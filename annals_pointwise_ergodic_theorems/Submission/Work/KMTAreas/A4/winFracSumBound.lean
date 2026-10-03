import Mathlib

namespace Work.KMTAreas.A4

open Finset

/-- For every `N ≥ 1`, the bilateral sum `∑_{m ∈ ℤ} N / (N + |m|)²` converges and is at most `5`.

The bound is proved by the elementary telescoping estimate
`N / (N + k + 1)² ≤ N (1/(N+k) - 1/(N+k+1))`, whose partial sums telescope to
`1 - N/(N+K) ≤ 1`; the symmetry `m ↦ -m` then gives the factor `2`, and the central
term contributes `1/N ≤ 1`. -/
theorem winFracSumBound :
    ∀ N : ℝ, 1 ≤ N → Summable (fun m : ℤ => N / (N + |(m : ℝ)|) ^ 2) ∧
      tsum (fun m : ℤ => N / (N + |(m : ℝ)|) ^ 2) ≤ 5 := by
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let f : ℤ → ℝ := fun m => N / (N + |(m : ℝ)|) ^ 2
  change Summable f ∧ tsum f ≤ 5
  -- Summability of the `ℕ`-indexed sequence `N / (N + n)^2`.
  have hbase : Summable (fun n : ℕ => N / (N + (n : ℝ)) ^ 2) := by
    have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h2 : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ 2) := by
      have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ)) ^ 2) 1).mpr h1
      simpa using h
    refine Summable.of_nonneg_of_le (f := fun n : ℕ => N / (((n + 1 : ℕ) : ℝ)) ^ 2)
      (g := fun n : ℕ => N / (N + (n : ℝ)) ^ 2) (fun n => by positivity) (fun n => ?_) ?_
    · apply div_le_div_of_nonneg_left hNpos.le (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      push_cast
      linarith
    · simpa [div_eq_mul_inv] using h2.mul_left N
  -- Summability over `ℤ`, from the two halves `ℕ` and `-ℕ`.
  have hsum : Summable f := by
    apply Summable.of_nat_of_neg
    · refine hbase.congr (fun n => ?_)
      show N / (N + (n : ℝ)) ^ 2 = f (n : ℤ)
      simp only [f, Int.cast_natCast]
      rw [abs_of_nonneg (Nat.cast_nonneg n)]
    · refine hbase.congr (fun n => ?_)
      show N / (N + (n : ℝ)) ^ 2 = f (-(n : ℤ))
      simp only [f, Int.cast_neg, Int.cast_natCast, abs_neg]
      rw [abs_of_nonneg (Nat.cast_nonneg n)]
  refine ⟨hsum, ?_⟩
  -- The summand is even, so the two-sided sum is the central term plus twice the half-line sum.
  have hEven : Function.Even f := by
    intro m
    simp only [f, Int.cast_neg, abs_neg]
  have hdec := tsum_int_eq_zero_add_two_mul_tsum_pnat hEven hsum
  -- The half-line sum is at most `1`, by telescoping.
  have hpnat : (∑' n : ℕ+, N / (N + ((n : ℕ) : ℝ)) ^ 2) ≤ 1 := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => N / (N + ((n : ℕ) : ℝ)) ^ 2)]
    refine Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun K => ?_)
    have hterm : ∀ i : ℕ, N / (N + (((i + 1 : ℕ) : ℝ))) ^ 2 ≤
        N * (1 / (N + (i : ℝ)) - 1 / (N + (((i + 1 : ℕ) : ℝ)))) := by
      intro i
      have hmain : N / (N + (i : ℝ) + 1) ^ 2 ≤ N * (1 / (N + (i : ℝ)) - 1 / (N + (i : ℝ) + 1)) := by
        have ha : 0 < N + (i : ℝ) := by positivity
        have hb : 0 < N + (i : ℝ) + 1 := by positivity
        field_simp
        nlinarith [ha, hb]
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hmain
    calc ∑ i ∈ range K, N / (N + (((i + 1 : ℕ) : ℝ))) ^ 2
        ≤ ∑ i ∈ range K, N * (1 / (N + (i : ℝ)) - 1 / (N + (((i + 1 : ℕ) : ℝ)))) :=
          sum_le_sum (fun i _ => hterm i)
      _ = N * (1 / N - 1 / (N + (K : ℝ))) := by
          rw [← mul_sum]
          congr 1
          have h := Finset.sum_range_sub' (fun i : ℕ => 1 / (N + (i : ℝ))) K
          simpa using h
      _ ≤ 1 := by
          have hNK : 0 ≤ N / (N + (K : ℝ)) := by positivity
          have hval : N * (1 / N - 1 / (N + (K : ℝ))) = 1 - N / (N + (K : ℝ)) := by
            field_simp
          rw [hval]
          linarith
  have hpnat2 : (∑' n : ℕ+, f (((n : ℕ) : ℤ))) ≤ 1 := by
    have heq : (fun n : ℕ+ => f (((n : ℕ) : ℤ))) =
        (fun n : ℕ+ => N / (N + ((n : ℕ) : ℝ)) ^ 2) := by
      funext n
      simp only [f, Int.cast_natCast]
      rw [abs_of_nonneg (Nat.cast_nonneg (n : ℕ))]
    rw [heq]; exact hpnat
  rw [hdec]
  have hf0 : f 0 = 1 / N := by
    simp only [f, Int.cast_zero, abs_zero, add_zero]
    field_simp
  rw [hf0]
  have hX : 2 • (∑' n : ℕ+, f (((n : ℕ) : ℤ))) ≤ 2 := by
    rw [two_nsmul]
    linarith
  have h1N : 1 / N ≤ 1 := by
    rw [div_le_one hNpos]; exact hN
  linarith

end Work.KMTAreas.A4
