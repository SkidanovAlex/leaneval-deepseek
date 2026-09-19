import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.PrimeNumberTheorem

/-- If `1 ≤ N` and `N ≤ N ^ (1/2)` (as reals) then `N = 1`.  Squaring `N ≤ √N` gives `N ^ 2 ≤ N`,
and since `N ≥ 1` this forces `N ≤ 1`. -/
private lemma nat_le_one_of_le_sqrt (N : ℕ) (hN : 1 ≤ N)
    (h : (N : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ)) : N = 1 := by
  have hx1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx0 : (0 : ℝ) ≤ (N : ℝ) := le_trans zero_le_one hx1
  have hs : (N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]; exact h
  have hsq : (N : ℝ) ^ 2 ≤ (N : ℝ) := by
    have h2 : (N : ℝ) ^ 2 ≤ (Real.sqrt (N : ℝ)) ^ 2 := by
      rw [sq_le_sq]
      rwa [abs_of_nonneg hx0, abs_of_nonneg (Real.sqrt_nonneg _)]
    rwa [Real.sq_sqrt hx0] at h2
  have hxle1 : (N : ℝ) ≤ 1 := by nlinarith [sq_nonneg ((N:ℝ) - 1)]
  have : (N : ℝ) = 1 := le_antisymm hxle1 hx1
  exact_mod_cast this

/-- The mass of `log p` over primes `p` in the window `[N + h, 2 * N + h]` that are not coprime
to `q` is at most `(1/2) * log N`, when `q ≤ √N`.  In fact the sum is `0`: a prime `p` in the
window that fails to be coprime to `q` must divide `q`, hence `N ≤ p ≤ q ≤ √N`, which is
impossible for `N ≥ 1`; the only surviving case `N = 1` forces `q = 1`, and then every integer is
coprime to `q`. -/
theorem not_coprime_prime_log_window_shift_le (N q h : ℕ) (hN : 1 ≤ N) (hq : q ≠ 0)
    (hqN : (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ)) :
    (∑ m ∈ (Finset.Icc (N + h) (2 * N + h)).filter (fun m => ¬ m.Coprime q),
        (if m.Prime then Real.log (m : ℝ) else 0)) ≤ (1 / 2) * Real.log (N : ℝ) := by
  have hsum0 : (∑ m ∈ (Finset.Icc (N + h) (2 * N + h)).filter (fun m => ¬ m.Coprime q),
        (if m.Prime then Real.log (m : ℝ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmIcc, hmcop⟩ := hm
    rw [Finset.mem_Icc] at hmIcc
    by_cases hmp : m.Prime
    · rw [if_pos hmp]
      exfalso
      have hm_ge_N : N ≤ m := by omega
      -- a prime `m` not coprime to `q` must divide `q`
      have hmgcd : m.gcd q ≠ 1 := fun hcontra =>
        hmcop (Nat.coprime_iff_gcd_eq_one.mpr hcontra)
      have heq : m.gcd q = m := by
        rcases hmp.eq_one_or_self_of_dvd (m.gcd q) (Nat.gcd_dvd_left m q) with h1 | h2
        · exact absurd h1 hmgcd
        · exact h2
      have hmdvdq : m ∣ q := heq ▸ Nat.gcd_dvd_right m q
      have hmleqq : m ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hmdvdq
      -- so `N ≤ m ≤ q ≤ √N`, forcing `N = 1`, hence `q = 1`, hence `m = 1`
      have hcast : (N : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
        calc (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge_N
          _ ≤ (q : ℝ) := by exact_mod_cast hmleqq
          _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := hqN
      have hN1 : N = 1 := nat_le_one_of_le_sqrt N hN hcast
      have hqle1 : q ≤ 1 := by
        have h1 : (q : ℝ) ≤ 1 := by
          calc (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := hqN
            _ = 1 := by rw [hN1]; norm_num
        exact_mod_cast h1
      have hmle1 : m ≤ 1 := le_trans hmleqq hqle1
      have hmge1 : 1 ≤ m := le_trans hN hm_ge_N
      have hm1 : m = 1 := le_antisymm hmle1 hmge1
      exact hmp.ne_one hm1
    · rw [if_neg hmp]
  rw [hsum0]
  exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hN))

end Commons.NumberTheory.PrimeNumberTheorem