import Mathlib
import Submission.Commons.NumberTheory.Sieve.LambdaR_prime

namespace Commons.NumberTheory.Sieve

open Finset

theorem LambdaR_eq_vonMangoldt_of_le {R n : ℕ} (hn : 2 ≤ n) (hnR : n ≤ R) :
    Commons.NumberTheory.Sieve.LambdaR R n = ArithmeticFunction.vonMangoldt n := by
  have hn0 : n ≠ 0 := by omega
  have hR0 : R ≠ 0 := by omega
  have hfilter : n.divisors.filter (fun d => d ≤ R) = n.divisors := by
    apply Finset.filter_true_of_mem
    intro d hd
    exact le_trans (Nat.divisor_le hd) hnR
  rw [LambdaR, hfilter]
  have hlog : ∀ d ∈ n.divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((R : ℝ) / (d : ℝ))
        = ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (R : ℝ)
          - ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (d : ℝ) := by
    intro d hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hd0 : (d : ℝ) ≠ 0 := by
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      exact_mod_cast hpos.ne'
    rw [Real.log_div (by exact_mod_cast hR0) hd0, mul_sub]
  rw [Finset.sum_congr rfl hlog, Finset.sum_sub_distrib]
  have h1 : (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (R : ℝ))
      = (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * Real.log (R : ℝ) :=
    (Finset.sum_mul _ _ _).symm
  have h2 : (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = 0 := by
    have hsum_eq : (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ))
        = (ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℝ) n := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
      simp
    rw [hsum_eq, ArithmeticFunction.coe_moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply_ne (by omega : n ≠ 1)]
  have h3 : (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (d : ℝ))
      = - ArithmeticFunction.vonMangoldt n := ArithmeticFunction.sum_moebius_mul_log_eq
  rw [h1, h2, h3]
  ring

end Commons.NumberTheory.Sieve
