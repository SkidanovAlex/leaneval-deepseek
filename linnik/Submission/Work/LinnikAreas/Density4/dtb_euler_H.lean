import Mathlib

/-!
# Euler product for `Σ_{d ∣ r} μ(d)² √d / φ(d)`

We prove the Euler product

`∑_{d ∣ r} μ(d)² √d / φ(d) = ∏_{p ∣ r} (1 + √p / (p - 1))`   (`r ≥ 1`),

by exhibiting `d ↦ μ(d)² √d / φ(d)` as a multiplicative arithmetic function `dtbFaf`
and convolving it with `ζ`, so that the divisor sum becomes the value of the
multiplicative function `dtbFaf * ζ` at `r`; the latter is evaluated by
`multiplicative_factorization` on the prime power `p ^ k` (`k ≥ 1`), where all
terms with `μ(p^i)² = 0` for `i ≥ 2` drop out.
-/

open Finset BigOperators

namespace Work.LinnikAreas.Density4

noncomputable section

/-- The multiplicative weight `d ↦ μ(d)² √d / φ(d)`, as an arithmetic function. -/
private noncomputable def dtbFaf : ArithmeticFunction ℝ :=
  ⟨fun n => ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * Real.sqrt (n : ℝ)
      / (Nat.totient n : ℝ), by simp⟩

private lemma isMult_dtbFaf : ArithmeticFunction.IsMultiplicative dtbFaf := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [dtbFaf], ?_⟩
  intro m n hm hn hcop
  simp only [dtbFaf, ArithmeticFunction.coe_mk]
  have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hcast : ((ArithmeticFunction.moebius (m * n) : ℝ))
      = (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius n : ℝ) := by
    rw [hmu]; push_cast; ring
  rw [hcast, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m), Nat.totient_mul hcop]
  have hmφ : (Nat.totient m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)).ne'
  have hnφ : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  push_cast
  field_simp

private lemma dtbFaf_one : dtbFaf 1 = 1 := by
  simp [dtbFaf, Nat.totient_one]

private lemma dtbFaf_prime (p : ℕ) (hp : p.Prime) :
    dtbFaf p = Real.sqrt (p : ℝ) / ((p : ℝ) - 1) := by
  simp only [dtbFaf, ArithmeticFunction.coe_mk]
  rw [ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
  have h2 : (((-1 : ℤ) : ℝ)) ^ 2 = 1 := by norm_num
  rw [h2, one_mul, Nat.cast_sub hp.one_le, Nat.cast_one]

private lemma dtbFaf_prime_pow_eq_zero (p i : ℕ) (hp : p.Prime) (hi : 2 ≤ i) :
    dtbFaf (p ^ i) = 0 := by
  simp only [dtbFaf, ArithmeticFunction.coe_mk]
  rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega : i ≠ 0),
    if_neg (by omega : ¬ i = 1)]
  simp

/-- The local factor: for a prime `p` and `k ≥ 1`, `(dtbFaf * ζ)(p ^ k) = 1 + √p/(p-1)`. -/
private lemma dtbFaf_mul_zeta_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    (dtbFaf * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (p ^ k)
      = 1 + Real.sqrt (p : ℝ) / ((p : ℝ) - 1) := by
  rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hk1 : k = (k - 1) + 1 := by omega
  rw [Finset.sum_range_succ' (fun x => dtbFaf (p ^ x)) k]
  rw [hk1, Finset.sum_range_succ' (fun x => dtbFaf (p ^ (x + 1))) (k - 1)]
  have hzero : (∑ x ∈ Finset.range (k - 1), dtbFaf (p ^ ((x + 1) + 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact dtbFaf_prime_pow_eq_zero p (x + 2) hp (by omega)
  rw [hzero]
  simp only [zero_add, pow_zero, pow_one]
  rw [dtbFaf_prime p hp, dtbFaf_one, add_comm]

private lemma dtbFaf_zeta_apply (n : ℕ) :
    (dtbFaf * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n
      = ∑ d ∈ n.divisors,
          ((ArithmeticFunction.moebius d : ℝ)) ^ 2 * Real.sqrt (d : ℝ)
            / (Nat.totient d : ℝ) := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  rfl

theorem dtb_euler_H (r : ℕ) (hr : 1 ≤ r) :
    (∑ d ∈ r.divisors,
        ((ArithmeticFunction.moebius d : ℝ)) ^ 2 * Real.sqrt (d : ℝ) / (Nat.totient d : ℝ))
      = ∏ p ∈ r.primeFactors, (1 + Real.sqrt (p : ℝ) / ((p : ℝ) - 1)) := by
  have hr0 : r ≠ 0 := by omega
  have hmult : ArithmeticFunction.IsMultiplicative
      (dtbFaf * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)) :=
    isMult_dtbFaf.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  rw [← dtbFaf_zeta_apply r,
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ hmult hr0]
  rw [show r.factorization.prod
        (fun p k => (dtbFaf * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (p ^ k))
      = ∏ p ∈ r.primeFactors,
          (dtbFaf * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ))
            (p ^ (r.factorization p)) from by
    simp only [Finsupp.prod, Nat.support_factorization]]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
  have hk : 1 ≤ r.factorization p := (hpp.dvd_iff_one_le_factorization hr0).mp hpdvd
  exact dtbFaf_mul_zeta_prime_pow p (r.factorization p) hpp hk

end

end Work.LinnikAreas.Density4
