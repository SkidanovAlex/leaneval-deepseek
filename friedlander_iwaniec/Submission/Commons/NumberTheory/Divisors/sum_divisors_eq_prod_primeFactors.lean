import Mathlib.Algebra.Order.Star.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

namespace Commons.NumberTheory.Divisors

open ArithmeticFunction

/-- The sum of a completely multiplicative function over the divisors of `n` factors as an
Euler-type product over the prime factors of `n`. -/
theorem sum_divisors_eq_prod_primeFactors (f : ℕ → ℤ) (hf1 : f 1 = 1)
    (hf : ∀ a b, f (a * b) = f a * f b) (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, f d)
      = ∏ p ∈ n.primeFactors, (∑ j ∈ Finset.range (n.factorization p + 1), f (p ^ j)) := by
  classical
  -- Extend `f` to an arithmetic function by sending `0` to `0`.
  let g : ArithmeticFunction ℤ := ⟨fun m => if m = 0 then 0 else f m, by simp⟩
  have hg_apply : ∀ m, g m = if m = 0 then 0 else f m := by
    intro m; simp [g, ArithmeticFunction.coe_mk]
  have hg1 : g 1 = 1 := by rw [hg_apply]; simp [hf1]
  -- `g` is multiplicative.
  have hgmul : g.IsMultiplicative := by
    refine ⟨hg1, ?_⟩
    intro m k hmk
    rcases eq_or_ne m 0 with rfl | hm
    · have hk1 : k = 1 := by simpa using hmk
      subst hk1
      simp [hg_apply]
    · rcases eq_or_ne k 0 with rfl | hk
      · have hm1 : m = 1 := by simpa using hmk.symm
        subst hm1
        simp [hg_apply]
      · rw [hg_apply, hg_apply, hg_apply, if_neg (mul_ne_zero hm hk), if_neg hm, if_neg hk, hf]
  -- Convolve with the constant-`1` function, so that we get the divisor sum.
  let F : ArithmeticFunction ℤ := (↑(ArithmeticFunction.zeta) : ArithmeticFunction ℤ) * g
  have hF_eq : F = (↑(ArithmeticFunction.zeta) : ArithmeticFunction ℤ) * g := rfl
  have hFmult : F.IsMultiplicative := by
    rw [hF_eq]
    exact (isMultiplicative_zeta.natCast).mul hgmul
  have hFval : ∀ m ≠ 0, F m = ∑ d ∈ m.divisors, f d := by
    intro m hm
    have h1 : F m = ∑ d ∈ m.divisors, g d := by
      rw [hF_eq]
      exact ArithmeticFunction.coe_zeta_smul_apply
    rw [h1]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hm (Nat.mem_divisors.mp hd).1
    rw [hg_apply, if_neg hd0]
  have hFpp : ∀ p k, p.Prime → F (p ^ k) = ∑ j ∈ Finset.range (k + 1), f (p ^ j) := by
    intro p k hp
    rw [hFval (p ^ k) (pow_ne_zero k hp.ne_zero)]
    exact Nat.sum_divisors_prime_pow hp
  rw [← hFval n hn]
  rw [hFmult.multiplicative_factorization F hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors (f := fun p k => F (p ^ k))]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [hFpp p (n.factorization p) (Nat.prime_of_mem_primeFactors hp)]

end Commons.NumberTheory.Divisors