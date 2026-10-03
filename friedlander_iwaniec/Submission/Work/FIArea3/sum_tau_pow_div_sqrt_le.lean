import Mathlib
import Submission.Work.FIArea2.sum_tau_pow_div_le

namespace Work.FIArea3

open Finset

/-- For every fixed `k` there is `C` with `∑_{n ≤ X} τ(n)^k/√n ≤ C √X (log X + 2)^{2^k}`.
This follows from the `1/n`-weighted companion `∑_{n ≤ X} τ(n)^k/n ≤ C (log X + 2)^{2^k}`
(supplied by `Work.FIArea2.sum_tau_pow_div_le`), since termwise
`τ(n)^k/√n = (τ(n)^k/n)·√n ≤ (τ(n)^k/n)·√X`. -/
theorem sum_tau_pow_div_sqrt_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ k / Real.sqrt (n : ℝ))
        ≤ C * Real.sqrt (X : ℝ) * (Real.log (X : ℝ) + 2) ^ (2 ^ k) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FIArea2.sum_tau_pow_div_le k
  refine ⟨C, hCpos, ?_⟩
  intro X
  set T := ∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ k / (n : ℝ) with hT
  have hST : (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ k / Real.sqrt (n : ℝ))
      ≤ Real.sqrt (X : ℝ) * T := by
    rw [hT, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨hn1, hnX⟩ := hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have htau : (0 : ℝ) ≤ ((n.divisors.card : ℝ)) ^ k := by positivity
    have hsqrtle : Real.sqrt (n : ℝ) ≤ Real.sqrt (X : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hnX)
    have hkey : ((n.divisors.card : ℝ)) ^ k / Real.sqrt (n : ℝ)
        = (((n.divisors.card : ℝ)) ^ k / (n : ℝ)) * Real.sqrt (n : ℝ) := by
      rw [div_eq_mul_one_div, ← Real.sqrt_div_self' (x := (n : ℝ))]
      ring
    calc ((n.divisors.card : ℝ)) ^ k / Real.sqrt (n : ℝ)
        = (((n.divisors.card : ℝ)) ^ k / (n : ℝ)) * Real.sqrt (n : ℝ) := hkey
      _ ≤ Real.sqrt (X : ℝ) * (((n.divisors.card : ℝ)) ^ k / (n : ℝ)) := by
          rw [mul_comm (Real.sqrt (X : ℝ))]
          exact mul_le_mul_of_nonneg_left hsqrtle (div_nonneg htau hnpos.le)
  calc (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ k / Real.sqrt (n : ℝ))
      ≤ Real.sqrt (X : ℝ) * T := hST
    _ ≤ Real.sqrt (X : ℝ) * (C * (Real.log (X : ℝ) + 2) ^ (2 ^ k)) :=
        mul_le_mul_of_nonneg_left (hC X) (Real.sqrt_nonneg _)
    _ = C * Real.sqrt (X : ℝ) * (Real.log (X : ℝ) + 2) ^ (2 ^ k) := by ring

end Work.FIArea3
