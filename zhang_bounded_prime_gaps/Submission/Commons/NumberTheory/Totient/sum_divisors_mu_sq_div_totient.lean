import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
import Submission.Commons.NumberTheory.Totient.prod_one_add_two_div_mul_pred_le_four

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.Totient

/-- The real-valued arithmetic function `d ↦ μ(d)²/φ(d)`: it is (coprime-)multiplicative
with value `1` at `1` and vanishes on all prime powers `p^k`, `k ≥ 2`. -/
private noncomputable def muSqDivTotient (d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / (Nat.totient d : ℝ)

private lemma muSqDivTotient_one : muSqDivTotient 1 = 1 := by
  simp [muSqDivTotient]

private lemma muSqDivTotient_mul (a b : ℕ) (hab : Nat.Coprime a b) :
    muSqDivTotient (a * b) = muSqDivTotient a * muSqDivTotient b := by
  have hmul : ArithmeticFunction.moebius (a * b) =
      ArithmeticFunction.moebius a * ArithmeticFunction.moebius b :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab
  have htot : (Nat.totient (a * b) : ℝ) =
      (Nat.totient a : ℝ) * (Nat.totient b : ℝ) := by
    rw [Nat.totient_mul hab, Nat.cast_mul]
  have hmu : ((ArithmeticFunction.moebius (a * b) : ℤ) : ℝ) =
      ((ArithmeticFunction.moebius a : ℤ) : ℝ) * ((ArithmeticFunction.moebius b : ℤ) : ℝ) := by
    rw [hmul]; push_cast; ring
  simp only [muSqDivTotient, hmu, htot]
  ring

private lemma muSqDivTotient_prime_pow (p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) :
    muSqDivTotient (p ^ k) = 0 := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hmu : ArithmeticFunction.moebius (p ^ k) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp hk0, if_neg hk1]
  simp [muSqDivTotient, hmu]

/-- For every `n ≠ 0`, `∏_{p | n} (1 + μ(p)²/φ(p)) = n/φ(n)`. -/
private lemma prod_one_add_muSqDivTotient_prime (n : ℕ) (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, (1 + muSqDivTotient p))
      = (n : ℝ) / (Nat.totient n : ℝ) := by
  -- Each factor equals `p / (p - 1)`.
  have hstep1 : (∏ p ∈ n.primeFactors, (1 + muSqDivTotient p))
      = ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hμ2 : ((ArithmeticFunction.moebius p : ℤ) : ℝ) ^ 2 = 1 := by
      rw [ArithmeticFunction.moebius_apply_prime hpp]; norm_num
    rw [muSqDivTotient, hμ2, Nat.totient_prime hpp]
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_le]; push_cast; ring
    have hxne : (p : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
      linarith
    rw [hcast]
    field_simp
    ring
  -- And `∏_{p | n} p/(p-1) = n/φ(n)`.
  have hstep2 : (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p - 1 : ℕ) : ℝ)))
      = (n : ℝ) / (Nat.totient n : ℝ) := by
    have hnat := Nat.totient_mul_prod_primeFactors n
    have hcast : (Nat.totient n : ℝ) * (∏ p ∈ n.primeFactors, (p : ℝ))
        = (n : ℝ) * (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ)) := by
      have h := congrArg (fun x : ℕ => (x : ℝ)) hnat
      simp only [Nat.cast_mul, Nat.cast_prod] at h
      exact h
    have hφ0 : (Nat.totient n : ℝ) ≠ 0 := by
      have : 0 < Nat.totient n := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
      exact_mod_cast this.ne'
    have hP0 : (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro p hp
      have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have : (1 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ p - 1 by have := hpp.two_le; omega)
      linarith
    rw [Finset.prod_div_distrib, div_eq_div_iff hP0 hφ0]
    rw [mul_comm]
    exact hcast
  rw [hstep1, hstep2]

theorem sum_divisors_mu_sq_div_totient (n : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ n.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / (Nat.totient d : ℝ))
      = (n : ℝ) / (Nat.totient n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hprod_sum :
      (∏ p ∈ n.primeFactors, (1 + muSqDivTotient p)) = ∑ d ∈ n.divisors, muSqDivTotient d :=
    Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
      muSqDivTotient n hn0 muSqDivTotient_one muSqDivTotient_mul muSqDivTotient_prime_pow
  calc
    (∑ d ∈ n.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / (Nat.totient d : ℝ))
        = ∑ d ∈ n.divisors, muSqDivTotient d := rfl
    _ = ∏ p ∈ n.primeFactors, (1 + muSqDivTotient p) := hprod_sum.symm
    _ = (n : ℝ) / (Nat.totient n : ℝ) := prod_one_add_muSqDivTotient_prime n hn0

end Commons.NumberTheory.Totient