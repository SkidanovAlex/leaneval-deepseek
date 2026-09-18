import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.PrimeCounting

namespace Commons.NumberTheory.Mertens

/-- The set of prime divisors of `n!` is exactly the set of primes `≤ n`. -/
lemma primeFactors_factorial_eq_primesLE (n : ℕ) :
    (n.factorial).primeFactors = n.primesLE := by
  ext p
  rw [Nat.mem_primeFactors, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hdvd, _⟩
    exact ⟨(hp.dvd_factorial).mp hdvd, hp⟩
  · rintro ⟨hle, hp⟩
    exact ⟨hp, (hp.dvd_factorial).mpr hle, Nat.factorial_ne_zero n⟩

theorem factorial_log_eq_sum_legendre (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ n.primesLE,
        (∑ i ∈ Finset.Ico 1 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ) := by
  have hprod_nat : n.factorial
      = ∏ p ∈ n.primesLE, p ^ ((n.factorial).factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization (Nat.factorial_ne_zero n)]
    rw [primeFactors_factorial_eq_primesLE]
  have hprod : (n.factorial : ℝ)
      = ∏ p ∈ n.primesLE, (p : ℝ) ^ ((n.factorial).factorization p) := by
    conv_lhs => rw [hprod_nat]
    push_cast
    rfl
  have hlog : Real.log (n.factorial : ℝ)
      = ∑ p ∈ n.primesLE, ((n.factorial).factorization p : ℝ) * Real.log (p : ℝ) := by
    rw [hprod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Real.log_pow]
    · intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
      exact pow_ne_zero _ (by exact_mod_cast hpp.pos.ne')
  rw [hlog]
  apply Finset.sum_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
  have hpn : p ≤ n := Nat.le_of_mem_primesLE hp
  have hp2 : 2 ≤ p := hpp.two_le
  have hn : n ≠ 0 := by omega
  have hloglt : Nat.log p n < n + 1 :=
    lt_of_lt_of_le (Nat.log_lt_self p hn) (Nat.le_succ n)
  have hfac : ((n.factorial).factorization p : ℝ)
      = ∑ i ∈ Finset.Ico 1 (n + 1), ((n / p ^ i : ℕ) : ℝ) := by
    rw [Nat.factorization_factorial hpp hloglt, Nat.cast_sum]
  rw [hfac]

end Commons.NumberTheory.Mertens