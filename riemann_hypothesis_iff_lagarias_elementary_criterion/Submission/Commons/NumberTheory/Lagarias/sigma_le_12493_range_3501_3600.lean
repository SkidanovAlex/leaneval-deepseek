import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases

namespace Commons.NumberTheory.Lagarias

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def sigmaFastAux : ℕ → ℕ → ℕ
  | _n, 0 => 0
  | n, k + 1 => sigmaFastAux n k + if n % (k + 1) = 0 then (k + 1) else 0

private def sigmaFast (n : ℕ) : ℕ := sigmaFastAux n n

private lemma sigmaFastAux_eq_sum (n k : ℕ) :
    sigmaFastAux n k = ∑ i ∈ Finset.Ico 1 (k + 1), if i ∣ n then i else 0 := by
  induction k with
  | zero =>
      simp [sigmaFastAux]
  | succ k ih =>
      rw [sigmaFastAux]
      rw [ih]
      rw [Finset.sum_Ico_succ_top (show 1 ≤ k + 1 by omega)]
      simp [Nat.dvd_iff_mod_eq_zero, add_comm]

private lemma sigma_eq_sigmaFast (n : ℕ) : (ArithmeticFunction.sigma 1 n : ℕ) = sigmaFast n := by
  rw [ArithmeticFunction.sigma_apply]
  unfold Nat.divisors
  rw [Finset.sum_filter]
  simp only [pow_one]
  rw [← sigmaFastAux_eq_sum n n]
  unfold sigmaFast
  rfl

theorem sigma_le_12493_range_3501_3600 (n : ℕ) (hL : 3501 ≤ n) (hU : n ≤ 3600) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 12493 := by
  rw [sigma_eq_sigmaFast]
  interval_cases n <;> decide

end Commons.NumberTheory.Lagarias