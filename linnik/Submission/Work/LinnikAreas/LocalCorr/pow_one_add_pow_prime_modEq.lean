import Mathlib

namespace Work.LinnikAreas.LocalCorr

/-- Auxiliary "lifting the exponent" step: for an odd prime `p`, `s ≥ 1` and any integer `u`,
`(1 + p^s u)^p ≡ 1 + p^(s+1) u  (mod p^(s+2))`.

This is the single-step content of LTE: raising `1 + p^s u` to the `p`-th power shifts the
valuation by exactly one.  It is proved from the binomial expansion, using that every term
`C(p,k) x^k` with `k ≥ 2` is divisible by `x^2`, together with the elementary fact `p ∣ C(p,k)`
for `0 < k < p`. -/
theorem pow_one_add_pow_prime_step (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {s : ℕ} (hs : 1 ≤ s)
    (u : ℤ) :
    (1 + (p : ℤ) ^ s * u) ^ p ≡ 1 + (p : ℤ) ^ (s + 1) * u [ZMOD (p : ℤ) ^ (s + 2)] := by
  have hp3 : 3 ≤ p := by have h := hp.two_le; omega
  have hp1 : 1 ≤ p := by omega
  set x : ℤ := (p : ℤ) ^ s * u with hxdef
  have hpx : (p : ℤ) ^ (s + 1) * u = (p : ℤ) * x := by
    rw [hxdef, pow_succ]; ring
  have hxpow : ∀ n : ℕ, x ^ n = (p : ℤ) ^ (s * n) * u ^ n := by
    intro n; rw [hxdef, mul_pow, pow_mul]
  have hopen : (1 + x) ^ p = ∑ k ∈ Finset.range (p + 1), x ^ k * (p.choose k : ℤ) := by
    rw [add_comm 1 x, add_pow]
    simp
  have hsplit : (1 + x) ^ p - (1 + (p : ℤ) * x)
      = ∑ k ∈ Finset.range (p - 1), x ^ (k + 2) * (p.choose (k + 2) : ℤ) := by
    rw [hopen, show p + 1 = 2 + (p - 1) from by omega, Finset.sum_range_add]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one, Nat.cast_one,
      mul_one, zero_add]
    ring_nf
  have hdvd : (p : ℤ) ^ (s + 2)
      ∣ ∑ k ∈ Finset.range (p - 1), x ^ (k + 2) * (p.choose (k + 2) : ℤ) := by
    apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_range] at hk
    have hk2 : k + 2 ≤ p := by omega
    rcases lt_or_eq_of_le hk2 with hlt | heq2
    · obtain ⟨c, hc⟩ := hp.dvd_choose_self (by omega : k + 2 ≠ 0) hlt
      rw [hc, hxpow (k + 2)]
      push_cast
      have hle : s + 2 ≤ s * (k + 2) + 1 := by
        have := Nat.mul_le_mul_left s (show 2 ≤ k + 2 by omega); omega
      have heq : (p : ℤ) ^ (s * (k + 2)) * u ^ (k + 2) * ((p : ℤ) * (c : ℤ))
          = (p : ℤ) ^ (s * (k + 2) + 1) * (u ^ (k + 2) * (c : ℤ)) := by
        rw [pow_succ]; ring
      rw [heq]
      exact (pow_dvd_pow (p : ℤ) hle).mul_right _
    · rw [heq2, Nat.choose_self, Nat.cast_one, mul_one, hxpow p]
      have hle : s + 2 ≤ s * p := by
        have := Nat.mul_le_mul_left s hp3; omega
      exact (pow_dvd_pow (p : ℤ) hle).mul_right _
  have hcong : (1 + (p : ℤ) ^ (s + 1) * u) ≡ (1 + x) ^ p [ZMOD (p : ℤ) ^ (s + 2)] := by
    apply Int.modEq_of_dvd
    rw [hpx, hsplit]
    exact hdvd
  exact hcong.symm

/-- **Lifting-the-exponent congruence for `1 + p^m`.**  For an odd prime `p` and `m ≥ 1`,
`(1 + p^m)^(p^j) ≡ 1 + p^(m+j)  (mod p^(m+j+1))` in `ℤ`.  This is the standard LTE statement
`v_p((1+p^m)^(p^j) − 1) = m + j` (for `p` odd); it is proved by induction on `j` using the
binomial expansion and the elementary fact `p ∣ C(p,k)` for `0 < k < p`.  It yields both
`(1+p^m)^(p^n) ≡ 1 (mod p^e)` and `(1+p^m)^(p^(n-1)) ≡ 1 + p^(e-1) (mod p^e)` when `m + n = e`,
i.e. that `1 + p^m` has order exactly `p^n` in `(ZMod (p^e))^*`. -/
theorem pow_one_add_pow_prime_modEq (p : ℕ) (hp : p.Prime) {m : ℕ} (hm : 1 ≤ m) (hp2 : p ≠ 2)
    (j : ℕ) :
    ((1 + (p : ℤ) ^ m) ^ (p ^ j)) ≡ (1 + (p : ℤ) ^ (m + j)) [ZMOD (p ^ (m + j + 1))] := by
  induction j with
  | zero => simp only [pow_zero, pow_one, Nat.add_zero]; rfl
  | succ j ih =>
    rw [show p ^ (j + 1) = p ^ j * p from pow_succ p j, pow_mul]
    obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp ih
    set u : ℤ := 1 - (p : ℤ) * t with hu
    have hXu : (1 + (p : ℤ) ^ m) ^ (p ^ j) = 1 + (p : ℤ) ^ (m + j) * u := by
      have h1 : (1 + (p : ℤ) ^ m) ^ (p ^ j)
          = 1 + (p : ℤ) ^ (m + j) - (p : ℤ) ^ (m + j + 1) * t := by
        linarith [ht]
      rw [h1, hu, pow_succ]; ring
    have hu1 : u ≡ 1 [ZMOD (p : ℤ)] := by
      rw [hu, Int.modEq_iff_dvd]
      have : (1 : ℤ) - (1 - (p : ℤ) * t) = (p : ℤ) * t := by ring
      rw [this]
      exact dvd_mul_right _ _
    have hmul : (p : ℤ) ^ (m + j + 1) * u ≡ (p : ℤ) ^ (m + j + 1)
        [ZMOD (p : ℤ) ^ (m + j + 2)] := by
      have h := Int.ModEq.mul_left' (c := (p : ℤ) ^ (m + j + 1)) hu1
      rwa [← pow_succ, mul_one] at h
    have hstep := pow_one_add_pow_prime_step p hp hp2 (s := m + j) (by omega) u
    rw [hXu]
    exact hstep.trans (Int.ModEq.add_left 1 hmul)

end Work.LinnikAreas.LocalCorr
