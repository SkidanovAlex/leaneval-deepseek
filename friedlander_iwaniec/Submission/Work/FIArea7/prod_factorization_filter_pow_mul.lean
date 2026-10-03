import Mathlib

namespace Work.FIArea7

lemma prod_factorization_filter_pow_mul (p e m : ℕ) (hp : p.Prime) (hm : ¬ p ∣ m) (hm0 : m ≠ 0) :
    ∏ q ∈ (p ^ e * m).primeFactors.filter (fun q => q % 4 = 1),
        ((p ^ e * m).factorization q + 1)
      = (if p % 4 = 1 then e + 1 else 1) *
        ∏ q ∈ m.primeFactors.filter (fun q => q % 4 = 1), (m.factorization q + 1) := by
  rcases e with _ | e'
  · -- `e = 0`: then `p ^ 0 * m = m`, and the extra factor is `1`.
    simp [pow_zero]
  · -- `e = e' + 1 ≥ 1`
    have hpf : (p ^ (e' + 1) * m).primeFactors = insert p m.primeFactors := by
      rw [Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) hm0,
          Nat.primeFactors_pow p (by omega), hp.primeFactors, Finset.singleton_union]
    -- `p` is not a prime factor of `m`
    have hnotmem : p ∉ m.primeFactors := fun h => hm (Nat.mem_primeFactors.mp h).2.1
    -- any prime factor `q` of `m` is different from `p`
    have hqne : ∀ q ∈ m.primeFactors, q ≠ p := by
      intro q hq h
      rw [h] at hq
      exact hm (Nat.mem_primeFactors.mp hq).2.1
    -- factorization off `p` agrees with that of `m`
    have hfac_ne : ∀ q, q ≠ p → (p ^ (e' + 1) * m).factorization q = m.factorization q := by
      intro q hq
      rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0]
      simp only [Finsupp.coe_add, Pi.add_apply]
      have h1 : (p ^ (e' + 1)).factorization q = 0 := by
        rw [Nat.factorization_pow, Finsupp.smul_apply, hp.factorization,
            Finsupp.single_eq_of_ne hq, smul_zero]
      rw [h1, zero_add]
    -- factorization at `p` is `e' + 1`
    have hfac_p : (p ^ (e' + 1) * m).factorization p = e' + 1 := by
      rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0]
      simp only [Finsupp.coe_add, Pi.add_apply]
      rw [Nat.factorization_pow_self hp, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
    rw [hpf]
    by_cases hp4 : p % 4 = 1
    · -- `p % 4 = 1`: the new prime factor `p` contributes a factor `e' + 1 + 1`
      rw [Finset.filter_insert, if_pos hp4]
      rw [if_pos hp4]
      rw [Finset.prod_insert (by intro h; exact hnotmem (Finset.mem_filter.mp h).1)]
      rw [hfac_p]
      congr 1
      apply Finset.prod_congr rfl
      intro q hq
      rw [hfac_ne q (hqne q (Finset.mem_filter.mp hq).1)]
    · -- `p % 4 ≠ 1`: the new prime factor `p` does not contribute
      rw [Finset.filter_insert, if_neg hp4]
      rw [if_neg hp4, one_mul]
      apply Finset.prod_congr rfl
      intro q hq
      rw [hfac_ne q (hqne q (Finset.mem_filter.mp hq).1)]

end Work.FIArea7
