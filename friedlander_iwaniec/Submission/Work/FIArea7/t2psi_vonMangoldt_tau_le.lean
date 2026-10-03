import Mathlib
import Submission.Work.FIArea7.sum_tau_Icc_le_two_mul_log

namespace Work.FIArea7

/-- **Trivial size of `Σ Λ(n) τ(n)`**: `∑_{n ≤ N} Λ(n) d(n) ≤ 4 N (log(N+2))^3`.
Proof route: `Λ(n) ≤ log n`, so the sum is at most `log N · ∑_{n≤N} τ(n)`, and the divisor sum is
`∑_{n≤N} τ(n) = ∑_{d≤N} ⌊N/d⌋ ≤ N(1 + log N)`
(`Submission.Commons.NumberTheory.ArithmeticFunction.sum_divisors_swap_hyperbola`).

Formalised route: `Λ n ≤ log n ≤ log(N+2) =: L` for `n ∈ Icc 1 N`, so the sum is at most
`L * ∑_{n≤N} τ(n)`, and the sharp summatory-divisor estimate
`Work.FIArea7.sum_tau_Icc_le_two_mul_log` gives `∑_{n≤N} τ(n) ≤ 2 N L`; finally
`2 N L^2 ≤ 4 N L^3` because `L ≥ log 2 > 1/2`. -/
theorem t2psi_vonMangoldt_tau_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n * ((n.divisors.card : ℕ) : ℝ))
      ≤ 4 * (N : ℝ) * (Real.log ((N : ℝ) + 2)) ^ (3 : ℕ) := by
  set L : ℝ := Real.log ((N : ℝ) + 2) with hLdef
  -- The logarithm is positive, so `Λ n ≤ log n ≤ L` gives the pointwise bound `Λ n * τ n ≤ L * τ n`.
  have hLpos : (0 : ℝ) < L := by
    rw [hLdef]
    exact Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hkey : (∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n * ((n.divisors.card : ℕ) : ℝ))
      ≤ L * (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hlog : Real.log (n : ℝ) ≤ L := by
      rw [hLdef]
      apply Real.log_le_log hnpos
      have : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      linarith
    exact mul_le_mul_of_nonneg_right
      (le_trans ArithmeticFunction.vonMangoldt_le_log hlog) (by positivity)
  -- The summatory divisor function is `≤ 2 N log(N+2) = 2 N L`.
  have htau : (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ)) ≤ 2 * (N : ℝ) * L := by
    rw [hLdef]
    exact sum_tau_Icc_le_two_mul_log N
  calc (∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n * ((n.divisors.card : ℕ) : ℝ))
      ≤ L * (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ)) := hkey
    _ ≤ L * (2 * (N : ℝ) * L) := mul_le_mul_of_nonneg_left htau hLpos.le
    _ = 2 * (N : ℝ) * L ^ 2 := by ring
    _ ≤ 4 * (N : ℝ) * L ^ 3 := by
        -- `L ≥ log 2 > 1/2`, hence `2 L - 1 ≥ 0` and `2 N L^2 ≤ 2 N L^2 (2L) = 4 N L^3`.
        have hLhalf : (1 / 2 : ℝ) ≤ L := by
          rw [hLdef]
          have h1 : Real.log 2 ≤ Real.log ((N : ℝ) + 2) :=
            Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) N])
          linarith [Real.log_two_gt_d9]
        have h1 : (0 : ℝ) ≤ 2 * (N : ℝ) * L ^ 2 := by positivity
        have h2 : (0 : ℝ) ≤ 2 * L - 1 := by linarith
        have hprod : (0 : ℝ) ≤ 2 * (N : ℝ) * L ^ 2 * (2 * L - 1) := mul_nonneg h1 h2
        nlinarith [hprod]

end Work.FIArea7
