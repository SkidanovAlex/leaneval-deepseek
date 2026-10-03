import Mathlib
import Submission.Commons.NumberTheory.DivisorSum.sum_divisor_count_asymptotic
import Submission.Commons.NumberTheory.DivisorSum.sum_divisor_count_div_le

namespace Commons.NumberTheory.DivisorSum

open Finset

/-- The sum of the number of divisors of all `n ≤ x` is at most `x * (1 + log x)`. -/
lemma sum_card_divisors_le (x : ℕ) (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℕ) : ℝ))
      ≤ (x : ℝ) * (1 + Real.log (x : ℝ)) := by
  rw [← Nat.cast_sum, sum_card_divisors_eq_sum_div, Nat.cast_sum]
  calc ∑ a ∈ Finset.Icc 1 x, ((x / a : ℕ) : ℝ)
      ≤ ∑ a ∈ Finset.Icc 1 x, (x : ℝ) / (a : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro a _
        exact Nat.cast_div_le
    _ = (x : ℝ) * ∑ a ∈ Finset.Icc 1 x, (1 : ℝ) / (a : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [mul_one_div]
    _ = (x : ℝ) * (harmonic x : ℝ) := by
        rw [harmonic_cast_eq_sum]
    _ ≤ (x : ℝ) * (1 + Real.log (x : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast harmonic_le_one_add_log x

theorem sum_tau_mul_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
      (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) * Real.log n)
        ≤ C * (x : ℝ) * (Real.log ((x : ℝ) + 1)) ^ 2 := by
  refine ⟨3, by norm_num, ?_⟩
  intro x hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hLpos : (0 : ℝ) < Real.log ((x : ℝ) + 1) :=
    Real.log_pos (by linarith)
  have hLnn : (0 : ℝ) ≤ Real.log ((x : ℝ) + 1) := le_of_lt hLpos
  -- Step A: replace `log n` by `log (x+1)`
  have hA : (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) * Real.log n)
      ≤ (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)))
          * Real.log ((x : ℝ) + 1) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro n hn
    obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hlog : Real.log (n : ℝ) ≤ Real.log ((x : ℝ) + 1) := by
      apply Real.log_le_log hnpos
      have hnx' : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hnx
      linarith
    have hc : (0 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hlog hc
  -- Step B: bound the unweighted divisor sum
  have hB := sum_card_divisors_le x hx
  -- `1 + log x ≤ 1 + log (x+1)`
  have hlogx : Real.log (x : ℝ) ≤ Real.log ((x : ℝ) + 1) :=
    Real.log_le_log hxpos (by linarith)
  have h1 : (1 : ℝ) + Real.log (x : ℝ) ≤ 1 + Real.log ((x : ℝ) + 1) := by linarith
  -- `1 + log (x+1) ≤ 3 log (x+1)` because `log (x+1) ≥ log 2 > 1/2`
  have htwo : (1 : ℝ) ≤ 2 * Real.log ((x : ℝ) + 1) := by
    have hbase : (1 : ℝ) < 2 * Real.log 2 := by
      have := Real.log_two_gt_d9; nlinarith
    have hge : (2 : ℝ) * Real.log 2 ≤ 2 * Real.log ((x : ℝ) + 1) := by
      have h2x : (2 : ℝ) ≤ (x : ℝ) + 1 := by exact_mod_cast (by omega : 2 ≤ x + 1)
      have : Real.log 2 ≤ Real.log ((x : ℝ) + 1) := Real.log_le_log (by norm_num) h2x
      linarith
    linarith
  have h3 : (1 : ℝ) + Real.log ((x : ℝ) + 1) ≤ 3 * Real.log ((x : ℝ) + 1) := by
    linarith
  calc (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) * Real.log n)
      ≤ (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ))) * Real.log ((x : ℝ) + 1) := hA
    _ ≤ ((x : ℝ) * (1 + Real.log (x : ℝ))) * Real.log ((x : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hB hLnn
    _ ≤ ((x : ℝ) * (1 + Real.log ((x : ℝ) + 1))) * Real.log ((x : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hxpos.le) hLnn
    _ ≤ ((x : ℝ) * (3 * Real.log ((x : ℝ) + 1))) * Real.log ((x : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hxpos.le) hLnn
    _ = 3 * (x : ℝ) * (Real.log ((x : ℝ) + 1)) ^ 2 := by ring

end Commons.NumberTheory.DivisorSum
