import Mathlib

namespace NK.TameData.Zhat

/-- Auxiliary arithmetic lemma: if `p` is a prime and `p ^ e ∣ N * u` with `p ∤ u`, then
`p ^ e ∣ N`.  (Since `p` is prime and coprime to `u`, the whole power `p ^ e` must already
divide `N`.) -/
lemma pow_dvd_of_dvd_mul {p : ℤ} (hp : Prime p) {u : ℤ} : ∀ {e : ℕ} {N : ℤ},
    ¬ p ∣ u → p^e ∣ N * u → p^e ∣ N := by
  intro e
  induction e with
  | zero => intro N hu h; simp
  | succ e ih =>
      intro N hu h
      have hpN : p ∣ N := by
        rcases hp.dvd_or_dvd ((dvd_pow_self p (Nat.succ_ne_zero e)).trans h) with h' | h'
        · exact h'
        · exact absurd h' hu
      obtain ⟨M, rfl⟩ := hpN
      have hpne : p ≠ 0 := hp.ne_zero
      have h1 : p^e ∣ M * u := by
        have hc : p * p^e ∣ p * (M * u) := by
          have heq : p * p^e = p^(e+1) := by rw [pow_succ]; ring
          rw [heq]
          have : (p * M) * u = p * (M * u) := by ring
          rwa [this] at h
        exact (mul_dvd_mul_iff_left hpne).mp hc
      have h3 : p^e ∣ M := ih hu h1
      rw [pow_succ]
      simpa [mul_comm] using mul_dvd_mul_right h3 p

/-- **Divisibility chain for `ℤ_ℓ`-valued sequences.**

Let `ℓ` be a prime and `N ≠ 0` a natural number.  Suppose a sequence `n : ℕ → ℤ` satisfies
`ℓ ^ j ∣ N * n j` and `ℓ ^ j ∣ n (j+1) - n j` for all `j ≥ 1`.  Then in fact `ℓ ^ k ∣ n k`
for every `k ≥ 1`: the factor `N` (which carries only a bounded amount of `ℓ`-adic
divisibility) can be discarded, and the divisibility of the successive differences forces the
`ℓ`-adic valuation of `n k` to grow at least as fast as `k`. -/
theorem dvd_of_dvd_chain {ℓ N : ℕ} (hℓ : ℓ.Prime) (hN : N ≠ 0) {n : ℕ → ℤ}
    (h1 : ∀ j, 1 ≤ j → (ℓ : ℤ) ^ j ∣ (N : ℤ) * n j)
    (h2 : ∀ j, 1 ≤ j → (ℓ : ℤ) ^ j ∣ n (j + 1) - n j) :
    ∀ k, 1 ≤ k → (ℓ : ℤ) ^ k ∣ n k := by
  have hp : Prime (ℓ : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]; simpa using hℓ
  have hpne : (ℓ : ℤ) ≠ 0 := hp.ne_zero
  intro k hk
  by_contra hbad
  -- `k` is a counterexample, so there is a *least* counterexample `K`.
  have hex : ∃ j, 1 ≤ j ∧ ¬ (ℓ : ℤ) ^ j ∣ n j := ⟨k, hk, hbad⟩
  have hKexists : ∃ K : ℕ, 1 ≤ K ∧ ¬ (ℓ : ℤ) ^ K ∣ n K ∧
      ∀ j, 1 ≤ j → j < K → (ℓ : ℤ) ^ j ∣ n j := by
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
    intro j hj hjt
    by_contra hjbad
    exact Nat.find_min hex hjt ⟨hj, hjbad⟩
  obtain ⟨K, hK1, hKbad, hmin⟩ := hKexists
  -- `n K` lies in `ℓ ^ (K-1) ℤ` but not in `ℓ ^ K ℤ`.
  have hbase : (ℓ : ℤ) ^ (K - 1) ∣ n K ∧ ¬ (ℓ : ℤ) ^ K ∣ n K := by
    refine ⟨?_, hKbad⟩
    rcases Nat.lt_or_ge 1 K with hK | hK
    · have hKm1 : 1 ≤ K - 1 := by omega
      have hKsucc : K - 1 + 1 = K := by omega
      have hd1 : (ℓ : ℤ) ^ (K - 1) ∣ n (K - 1 + 1) - n (K - 1) := h2 (K - 1) hKm1
      rw [hKsucc] at hd1
      have hd2 : (ℓ : ℤ) ^ (K - 1) ∣ n (K - 1) := hmin (K - 1) hKm1 (by omega)
      have := dvd_add hd1 hd2
      rwa [sub_add_cancel] at this
    · have hKeq : K = 1 := by omega
      rw [hKeq]; simp
  -- The "defect" propagates: the same two facts hold for every `m ≥ K`.
  have hR : ∀ m, K ≤ m → (ℓ : ℤ) ^ (K - 1) ∣ n m ∧ ¬ (ℓ : ℤ) ^ K ∣ n m := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
        intro hm
        by_cases hmK : m < K
        · have hmeq : m + 1 = K := by omega
          rw [hmeq]; exact hbase
        · have hmK' : K ≤ m := by omega
          obtain ⟨ha, hna⟩ := ih hmK'
          have hd := h2 m (by omega)
          refine ⟨?_, ?_⟩
          · have h1' : (ℓ : ℤ) ^ (K - 1) ∣ (ℓ : ℤ) ^ m := pow_dvd_pow _ (by omega)
            have := dvd_add (h1'.trans hd) ha
            rwa [sub_add_cancel] at this
          · intro hcon
            apply hna
            have h2' : (ℓ : ℤ) ^ K ∣ n (m + 1) - n m := (pow_dvd_pow _ hmK').trans hd
            have := dvd_sub hcon h2'
            rwa [sub_sub_cancel] at this
  -- Write `n (K+N) = ℓ ^ (K-1) * u` with `ℓ ∤ u`.
  obtain ⟨u, hu⟩ := (hR (K + N) (by omega)).1
  have hpu : ¬ (ℓ : ℤ) ∣ u := by
    intro hdu
    apply (hR (K + N) (by omega)).2
    have hEq : (ℓ : ℤ) ^ K = (ℓ : ℤ) ^ (K - 1) * (ℓ : ℤ) := by
      conv_lhs => rw [show K = K - 1 + 1 by omega]
      rw [pow_succ]
    rw [hu, hEq]
    exact mul_dvd_mul_left _ hdu
  -- Hypothesis `h1` at `K + N` then forces `ℓ ^ (N+1) ∣ N`.
  have h1K : (ℓ : ℤ) ^ (K + N) ∣ (N : ℤ) * n (K + N) := h1 (K + N) (by omega)
  have hdvd : (ℓ : ℤ) ^ (N + 1) ∣ (N : ℤ) * u := by
    have he : K + N = (K - 1) + (N + 1) := by omega
    have h₁ : (ℓ : ℤ) ^ ((K - 1) + (N + 1)) ∣ (N : ℤ) * n (K + N) := by
      rw [← he]; exact h1K
    rw [hu] at h₁
    rw [pow_add] at h₁
    have hr : (N : ℤ) * ((ℓ : ℤ) ^ (K - 1) * u) = (ℓ : ℤ) ^ (K - 1) * ((N : ℤ) * u) := by
      ring
    rw [hr] at h₁
    exact (mul_dvd_mul_iff_left (pow_ne_zero (K - 1) hpne)).mp h₁
  have hN1 : (ℓ : ℤ) ^ (N + 1) ∣ (N : ℤ) := pow_dvd_of_dvd_mul hp hpu hdvd
  have hNdvd : ℓ ^ (N + 1) ∣ N := by
    have hcast : ((ℓ ^ (N + 1) : ℕ) : ℤ) ∣ (N : ℤ) := by simpa using hN1
    exact Int.natCast_dvd_natCast.mp hcast
  -- But `ℓ ^ (N+1) ∣ N` is impossible for `0 < N`.
  have hle : ℓ ^ (N + 1) ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hNdvd
  have h2le : 2 ^ (N + 1) ≤ ℓ ^ (N + 1) := Nat.pow_le_pow_left hℓ.two_le (N + 1)
  have hlt : N < 2 ^ (N + 1) :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ N))
  omega

end NK.TameData.Zhat
