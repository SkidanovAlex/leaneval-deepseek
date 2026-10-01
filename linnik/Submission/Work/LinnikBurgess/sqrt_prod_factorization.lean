import Mathlib
import Submission.Work.LinnikBurgess.singleton_ssa_defs

/-!
# Factoring the square root of `q` over the low/high prime sets

Writing `e_p = q.factorization p`, this file proves

`(∏_{p ∈ lowPrimeSet q} √p) * (∏_{p ∈ highPrimeSet q} p^{e_p/2}) = √q`,

i.e. the square root of a positive integer splits, over its prime factors, into the
square roots of the primes occurring to the first power and the `e_p/2`-powers of the
remaining primes.  The two auxiliary statements used are the elementary identity
`√(x^n) = x^(n/2)` for `x ≥ 0` and the fact that on `q.primeFactors` the condition
`e_p ≠ 1` is equivalent to `2 ≤ e_p` (the high prime set).
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

/-- For a nonnegative real `x` and `n : ℕ`, `√(x ^ n) = x ^ (n / 2)`, the exponent on
the right being a real number. -/
lemma sqrt_pow_eq_rpow_div_two {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = x ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x n, ← Real.rpow_mul hx ((n : ℝ)) (1 / 2)]
  congr 1
  ring

/-- On `q.primeFactors`, a prime has exponent `≠ 1` exactly when its exponent is `≥ 2`:
this identifies `highPrimeSet q` with the complement of the exponents-`1` filter. -/
lemma highPrimeSet_eq_filter_not (q : ℕ) (hq : q ≠ 0) :
    highPrimeSet q = q.primeFactors.filter (fun p => ¬ (q.factorization p = 1)) := by
  ext p
  simp only [highPrimeSet, Finset.mem_filter]
  constructor
  · rintro ⟨hp, h2⟩; exact ⟨hp, by omega⟩
  · rintro ⟨hp, hne⟩
    obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
    have hpos : 0 < q.factorization p := hpp.factorization_pos_of_dvd hq hpdvd
    exact ⟨hp, by omega⟩

theorem sqrt_prod_factorization {q : ℕ} (hq : 0 < q) :
    (∏ p ∈ lowPrimeSet q, Real.sqrt (p : ℝ))
      * (∏ p ∈ highPrimeSet q, (p : ℝ) ^ ((q.factorization p : ℝ) / 2))
      = Real.sqrt (q : ℝ) := by
  have hqne : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  -- Split the product over the primes of `q` into the `e_p = 1` part (weight `√p`)
  -- and the complementary part (weight `p^{e_p/2}`).
  have hsplit :
      (∏ p ∈ q.primeFactors.filter (fun p => q.factorization p = 1), Real.sqrt (p : ℝ))
        * (∏ p ∈ q.primeFactors.filter (fun p => ¬ (q.factorization p = 1)),
            (p : ℝ) ^ ((q.factorization p : ℝ) / 2))
        = ∏ p ∈ q.primeFactors,
            (if q.factorization p = 1 then Real.sqrt (p : ℝ)
             else (p : ℝ) ^ ((q.factorization p : ℝ) / 2)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not q.primeFactors
          (fun p => q.factorization p = 1)
          (fun p => if q.factorization p = 1 then Real.sqrt (p : ℝ)
                    else (p : ℝ) ^ ((q.factorization p : ℝ) / 2))]
    congr 1
    · apply Finset.prod_congr rfl
      intro p hp
      simp only [Finset.mem_filter] at hp
      rw [if_pos hp.2]
    · apply Finset.prod_congr rfl
      intro p hp
      simp only [Finset.mem_filter] at hp
      rw [if_neg hp.2]
  -- On the primes of `q` with `e_p = 1`, `√p = p^{e_p/2}`.
  have hstep3 :
      (∏ p ∈ q.primeFactors,
          (if q.factorization p = 1 then Real.sqrt (p : ℝ)
           else (p : ℝ) ^ ((q.factorization p : ℝ) / 2)))
        = ∏ p ∈ q.primeFactors, (p : ℝ) ^ ((q.factorization p : ℝ) / 2) := by
    apply Finset.prod_congr rfl
    intro p hp
    by_cases h : q.factorization p = 1
    · rw [if_pos h, h, Real.sqrt_eq_rpow]
      norm_num
    · rw [if_neg h]
  -- `∏_p p^{e_p/2} = √(∏_p p^{e_p}) = √q`, using the prime factorization of `q`.
  have hstep4 :
      (∏ p ∈ q.primeFactors, (p : ℝ) ^ ((q.factorization p : ℝ) / 2))
        = Real.sqrt (q : ℝ) := by
    have hq_eq : q = ∏ p ∈ q.primeFactors, p ^ q.factorization p :=
      Nat.prod_primeFactors_pow_factorization hqne
    have hcast : ((q : ℕ) : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) ^ q.factorization p := by
      conv_lhs => rw [hq_eq]
      rw [Nat.cast_prod]
      exact Finset.prod_congr rfl (fun p _ => by rw [Nat.cast_pow])
    conv_rhs => rw [hcast]
    rw [Real.sqrt_prod q.primeFactors
          (x := fun p => (p : ℝ) ^ q.factorization p) (fun p _ => by positivity)]
    exact Finset.prod_congr rfl
      (fun p _ => by rw [sqrt_pow_eq_rpow_div_two (Nat.cast_nonneg p) (q.factorization p)])
  rw [show lowPrimeSet q = q.primeFactors.filter (fun p => q.factorization p = 1) from rfl,
      highPrimeSet_eq_filter_not q hqne, hsplit, hstep3, hstep4]

end Work.LinnikBurgess
