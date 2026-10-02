import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Submission.Commons.Data.Nat.mul_factorization_of_dvd_left

namespace Commons.NumberTheory.Nat

/-- For a prime `p`, exponent `a ≥ 3` and `m ≠ 0` coprime to `p`, the product of the
prime powers `q ^ v_q(n)` over the primes `q` whose exponent in `n = p ^ a * m` is at
least `3` splits as `p ^ a` times the analogous product over the factor `m`:
the primes of `p` and `m` are disjoint, and `v_q(p ^ a * m) = v_q(m)` for `q ∣ m`. -/
theorem prod_primeFactors_filter_factorization_mul_prime_pow {p a m : ℕ} (hp : p.Prime)
    (ha : 3 ≤ a) (hm : m ≠ 0) (hcop : p.Coprime m) :
    (∏ q ∈ (p ^ a * m).primeFactors.filter (fun q => 3 ≤ (p ^ a * m).factorization q),
        q ^ (p ^ a * m).factorization q)
      = p ^ a * (∏ q ∈ m.primeFactors.filter (fun q => 3 ≤ m.factorization q),
        q ^ m.factorization q) := by
  have hk : p ^ a ≠ 0 := pow_ne_zero a hp.ne_zero
  have hkm : (p ^ a).Coprime m := hcop.pow_left a
  -- `p` does not divide `m`.
  have hp_notmem : p ∉ m.primeFactors := by
    rw [Nat.mem_primeFactors]
    rintro ⟨-, hdvd, -⟩
    exact (hp.coprime_iff_not_dvd.mp hcop) hdvd
  -- The prime factors of `p ^ a * m` are those of `m` plus `p`.
  have hpf : (p ^ a * m).primeFactors = insert p m.primeFactors := by
    rw [Nat.primeFactors_mul hk hm, @Nat.primeFactors_pow a p (by omega), hp.primeFactors,
      Finset.singleton_union]
  -- For `q ∣ m`, the exponent of `q` in `p ^ a * m` equals its exponent in `m`.
  have hmul_fact : ∀ q ∈ m.primeFactors, (p ^ a * m).factorization q = m.factorization q := by
    intro q hq
    obtain ⟨hqprime, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
    rw [mul_comm (p ^ a) m]
    exact Commons.Data.Nat.mul_factorization_of_dvd_left hkm.symm hqprime hqdvd
  -- The exponent of `p` itself is `a ≥ 3`.
  have hfactp : (p ^ a * m).factorization p = a := by
    rw [Nat.factorization_mul_apply_of_coprime hkm, Nat.factorization_pow_self hp,
      Nat.factorization_eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.mp hcop)]
    simp
  have hCp : 3 ≤ (p ^ a * m).factorization p := by rw [hfactp]; exact ha
  -- The filter over `m.primeFactors` agrees with the one using `m.factorization`.
  have hfilter : m.primeFactors.filter (fun q => 3 ≤ (p ^ a * m).factorization q)
      = m.primeFactors.filter (fun q => 3 ≤ m.factorization q) := by
    apply Finset.filter_congr
    intro q hq
    rw [hmul_fact q hq]
  rw [hpf, Finset.filter_insert, if_pos hCp, hfilter]
  rw [Finset.prod_insert (by simp [Finset.mem_filter, hp_notmem])]
  rw [hfactp]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  rw [hmul_fact q (Finset.mem_of_mem_filter q hq)]

end Commons.NumberTheory.Nat