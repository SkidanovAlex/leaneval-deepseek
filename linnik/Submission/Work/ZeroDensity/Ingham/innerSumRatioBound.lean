import Mathlib
import Submission.Work.ZeroDensity.Montgomery.divisorsCardDivSum_le

namespace Work.ZeroDensity.Ingham

/-- For `1 ≤ m ≤ N`: `∑_{n=m+1}^{N} n/(n-m) ≤ N + m (1 + log N)`. Write `n/(n-m) = 1 + m/(n-m)`,
reindex `n ↦ n-m`, and use `Work.ZeroDensity.Montgomery.sum_Ioc_inv_le_one_add_log`. -/
theorem innerSumRatioBound (m N : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) :
    ∑ n ∈ Finset.Icc (m+1) N, ((n : ℝ) / ((n : ℝ) - (m : ℝ)))
      ≤ (N : ℝ) + (m : ℝ) * (1 + Real.log (N : ℝ)) := by
  -- Reindex `n ↦ n - m` and rewrite `n/(n-m) = 1 + m/(n-m)`.
  have hmain : ∑ n ∈ Finset.Icc (m+1) N, ((n : ℝ) / ((n : ℝ) - (m : ℝ)))
      = ∑ d ∈ Finset.Icc 1 (N - m), (1 + (m : ℝ) / (d : ℝ)) := by
    refine Finset.sum_bij (fun n _ => n - m) ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      obtain ⟨h1, h2⟩ := hn
      omega
    · intro n1 hn1 n2 hn2 h
      rw [Finset.mem_Icc] at hn1 hn2
      omega
    · intro d hd
      rw [Finset.mem_Icc] at hd
      obtain ⟨h1, h2⟩ := hd
      refine ⟨d + m, ?_, ?_⟩
      · rw [Finset.mem_Icc]; omega
      · omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      obtain ⟨h1, h2⟩ := hn
      have hmn : m ≤ n := by omega
      have hk : ((n - m : ℕ) : ℝ) ≠ 0 := by
        rw [Nat.cast_ne_zero]; omega
      have hn_eq : (n : ℝ) = ((n - m : ℕ) : ℝ) + (m : ℝ) := by
        rw [← Nat.cast_add, Nat.sub_add_cancel hmn]
      rw [← Nat.cast_sub hmn, hn_eq, add_div, div_self hk]
  rw [hmain]
  -- Bound the reciprocal sum by `1 + log N` via the `Ioc 0 N` estimate.
  have hS : ∑ d ∈ Finset.Icc 1 (N - m), (1 / (d : ℝ)) ≤ 1 + Real.log (N : ℝ) := by
    have hsub : Finset.Icc 1 (N - m) ⊆ Finset.Ioc 0 N := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      rw [Finset.mem_Ioc]
      omega
    calc ∑ d ∈ Finset.Icc 1 (N - m), (1 / (d : ℝ))
        ≤ ∑ d ∈ Finset.Ioc 0 N, (1 / (d : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => by rw [one_div]; positivity)
      _ ≤ 1 + Real.log (N : ℝ) :=
          Work.ZeroDensity.Montgomery.sum_Ioc_inv_le_one_add_log N
  have hcard : ((Finset.Icc 1 (N - m)).card : ℝ) ≤ (N : ℝ) := by
    have : (Finset.Icc 1 (N - m)).card = N - m := by rw [Nat.card_Icc]; omega
    rw [this]; exact_mod_cast Nat.sub_le N m
  have hsum_eq : ∑ d ∈ Finset.Icc 1 (N - m), (1 + (m : ℝ) / (d : ℝ))
      = ((Finset.Icc 1 (N - m)).card : ℝ)
        + (m : ℝ) * ∑ d ∈ Finset.Icc 1 (N - m), (1 / (d : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    · apply Finset.sum_congr rfl
      intro d hd
      rw [div_eq_mul_inv, one_div]
  rw [hsum_eq]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have := mul_le_mul_of_nonneg_left hS hm0
  linarith

end Work.ZeroDensity.Ingham
