import Mathlib
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le

namespace Work.FIArea2

/-- The companion of `Commons.NumberTheory.DivisorSum.sum_tau_pow_le` for the harmonic-weighted sum: for every fixed `k` there is `C` with `∑_{n ≤ X} τ(n)^k/n ≤ C (log X + 2)^{2^k}`.  (`Submission/Commons/NumberTheory/DivisorSum/sum_tau_pow_le.lean` proves the companion `∑_{n≤x} τ(n)^k ≤ C x (log(x+1))^{2^k−1}`, together with a `Tsum`-based argument for the `1/n`-weighted sum; the sharp exponent here is `2^k`.) -/
theorem sum_tau_pow_div_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ k / (n : ℝ))
        ≤ C * (Real.log (X : ℝ) + 2) ^ (2 ^ k) := by
  obtain ⟨C, hCpos, hC⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le k
  refine ⟨C, hCpos, ?_⟩
  intro X
  rcases Nat.eq_zero_or_pos X with hX | hX
  · subst hX
    have hsum : (∑ n ∈ Finset.Icc 1 (0 : ℕ), ((n.divisors.card : ℝ)) ^ k / (n : ℝ)) = 0 := by
      simp
    have hlog : Real.log ((0 : ℕ) : ℝ) = 0 := by simp
    rw [hsum, hlog]
    positivity
  · have h1 : (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ k / (n : ℝ))
        ≤ C * (Real.log ((X : ℝ) + 2)) ^ (2 ^ k) := hC X (by omega)
    have hr1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hbase : Real.log ((X : ℝ) + 2) ≤ Real.log (X : ℝ) + 2 := by
      rw [Real.log_le_iff_le_exp (by linarith)]
      rw [Real.exp_add, Real.exp_log (by linarith)]
      have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
        have h := Real.add_one_le_exp (2 : ℝ); linarith
      have hr0 : (0 : ℝ) ≤ (X : ℝ) := by linarith
      have h3r : (3 : ℝ) * (X : ℝ) ≤ (X : ℝ) * Real.exp 2 := by
        have h := mul_le_mul_of_nonneg_left hexp2 hr0
        linarith
      have hX2 : (X : ℝ) + 2 ≤ 3 * (X : ℝ) := by linarith
      linarith
    have hX2nn : 0 ≤ Real.log ((X : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hpow : (Real.log ((X : ℝ) + 2)) ^ (2 ^ k) ≤ (Real.log (X : ℝ) + 2) ^ (2 ^ k) :=
      pow_le_pow_left₀ hX2nn hbase (2 ^ k)
    calc (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ k / (n : ℝ))
        ≤ C * (Real.log ((X : ℝ) + 2)) ^ (2 ^ k) := h1
      _ ≤ C * (Real.log (X : ℝ) + 2) ^ (2 ^ k) :=
          mul_le_mul_of_nonneg_left hpow hCpos.le

end Work.FIArea2
