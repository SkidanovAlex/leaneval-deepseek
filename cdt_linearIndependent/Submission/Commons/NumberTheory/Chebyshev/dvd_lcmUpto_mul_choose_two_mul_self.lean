import Mathlib.NumberTheory.Chebyshev
import Submission.Commons.NumberTheory.Chebyshev.lcmUpto_even_dvd_binom_mul

namespace Commons.NumberTheory.Chebyshev

/-- `n * C(2n, n)` divides `lcmUpto (2n)`, the least common multiple of `{1, …, 2n}`.

The proof is `p`-adic.  For a prime `p`, writing `e = v_p(n)` and `a = log_p (2n)`, Kummer's
theorem (`Nat.factorization_choose`) exhibits `v_p(C(2n, n))` as the cardinality of
`S = {i ∈ {1,…,a} : p ^ i ≤ 2 * (n % p ^ i)}`.  Every `i ∈ S` must satisfy `e < i`, because for
`i ≤ e` one has `p ^ i ∣ n`, whence `n % p ^ i = 0` and the defining inequality of `S` fails.
Hence `S ⊆ {e+1, …, a}`, so `v_p(C(2n, n)) ≤ a - e` and `v_p(n) + v_p(C(2n, n)) ≤ a`. -/
theorem dvd_lcmUpto_mul_choose_two_mul_self (n : ℕ) (hn : 1 ≤ n) :
    n * Nat.choose (2 * n) n ∣ Nat.lcmUpto (2 * n) := by
  have hn0 : n ≠ 0 := by omega
  have hc0 : Nat.choose (2 * n) n ≠ 0 := Nat.choose_ne_zero (by omega)
  rw [← Nat.factorization_prime_le_iff_dvd (Nat.mul_ne_zero hn0 hc0) (Nat.lcmUpto_ne_zero (2 * n))]
  intro p hp
  rw [Nat.factorization_mul hn0 hc0, Finsupp.add_apply, Nat.factorization_lcmUpto (2 * n) hp]
  rw [Nat.factorization_choose (n := 2 * n) (k := n) (b := Nat.log p (2 * n) + 1) hp
        (by omega) (by omega)]
  have h2n : 2 * n - n = n := by omega
  rw [h2n]
  -- Reduce to a cardinality statement.
  set a := Nat.log p (2 * n) with ha
  set e := n.factorization p with he
  set S := (Finset.Ico 1 (a + 1)).filter (fun i => p ^ i ≤ n % p ^ i + n % p ^ i) with hS
  have hea : e ≤ a := by
    rw [he, ha]
    have hdvd : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
    have hle : p ^ n.factorization p ≤ n := Nat.le_of_dvd (by omega) hdvd
    exact Nat.le_log_of_pow_le hp.one_lt (by omega)
  have hsub : S ⊆ Finset.Ico (e + 1) (a + 1) := by
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    obtain ⟨hi1, hcond⟩ := hi
    rw [Finset.mem_Ico] at hi1 ⊢
    obtain ⟨hge1, hlt⟩ := hi1
    refine ⟨?_, hlt⟩
    by_contra hcon
    have hile : i ≤ e := by omega
    have hidvd : p ^ i ∣ n :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hn0).mpr (by omega)
    have hmod : n % p ^ i = 0 := Nat.dvd_iff_mod_eq_zero.mp hidvd
    rw [hmod] at hcond
    have hpos : 0 < p ^ i := pow_pos hp.pos i
    omega
  have hcard : S.card ≤ a - e := by
    have h := Finset.card_le_card hsub
    rw [Nat.card_Ico, Nat.add_sub_add_right] at h
    exact h
  have hfinal : e + S.card ≤ e + (a - e) := Nat.add_le_add_left hcard e
  rw [Nat.add_sub_cancel' hea] at hfinal
  exact hfinal

end Commons.NumberTheory.Chebyshev