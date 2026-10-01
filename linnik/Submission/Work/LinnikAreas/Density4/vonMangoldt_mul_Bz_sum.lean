import Mathlib
import Submission.Work.LinnikAreas.Density4.LamRDefs

namespace Work.LinnikAreas.Density4

open Finset

noncomputable section

/-- **`B_z` on a prime power.**  For a prime `p`, `m ≥ 1` and `z ≥ 1`,
`B_z(p^m) = -log(p/z)` when `p > z` and `0` otherwise: the divisors of `p^m` are the powers
`p^j` (`j ≤ m`), of which only `j = 0, 1` have `μ ≠ 0`, and `p^0 = 1 ≤ z`. -/
lemma Bz_apply_prime_pow (z p m : ℕ) (hp : Nat.Prime p) (hm : 1 ≤ m) (hz : 1 ≤ z) :
    Bz z (p^m) = if z < p then -Real.log ((p:ℝ)/(z:ℝ)) else 0 := by
  unfold Bz
  set s := (p^m).divisors.filter (fun d => z < d) with hs
  have hmem : ∀ d, d ∈ s ↔ d ∣ p^m ∧ z < d := by
    intro d
    rw [hs, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, pow_ne_zero m hp.pos.ne'⟩, h.2⟩⟩
  have h1 : ∀ b ∈ s, b ≠ p → (ArithmeticFunction.moebius b : ℝ) * Real.log ((b:ℝ)/(z:ℝ)) = 0 := by
    intro b hb hbp
    obtain ⟨hbd, hbz⟩ := (hmem b).mp hb
    have hb1 : b ≠ 1 := by rintro rfl; simp at hbz; omega
    obtain ⟨k, hkm, hbk⟩ := (Nat.dvd_prime_pow hp).mp hbd
    subst hbk
    have hk0 : k ≠ 0 := by rintro rfl; simp at hb1
    have hk1 : k ≠ 1 := by rintro rfl; exact hbp (by rw [pow_one])
    rw [ArithmeticFunction.moebius_apply_prime_pow hp hk0, if_neg hk1]
    simp
  have hsum : ∑ d ∈ s, (ArithmeticFunction.moebius d : ℝ) * Real.log ((d:ℝ)/(z:ℝ))
      = if p ∈ s then (ArithmeticFunction.moebius p : ℝ) * Real.log ((p:ℝ)/(z:ℝ)) else 0 := by
    rw [show ∑ d ∈ s, (ArithmeticFunction.moebius d : ℝ) * Real.log ((d:ℝ)/(z:ℝ))
        = ∑ d ∈ s, (if d = p then (ArithmeticFunction.moebius p : ℝ) * Real.log ((p:ℝ)/(z:ℝ)) else 0) from
      Finset.sum_congr rfl (fun d hd => by
        by_cases h : d = p
        · subst h; simp
        · simp [h, h1 d hd h])]
    rw [Finset.sum_ite_eq' s p (fun _ => (ArithmeticFunction.moebius p : ℝ) * Real.log ((p:ℝ)/(z:ℝ)))]
  rw [hsum]
  have hmem_p : (p ∈ s) ↔ z < p := by
    rw [hmem]; constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨dvd_pow_self p (by omega), h⟩
  by_cases hzp : z < p
  · rw [if_pos (hmem_p.mpr hzp), if_pos hzp, ArithmeticFunction.moebius_apply_prime hp]
    push_cast; ring
  · rw [if_neg (fun h => hzp (hmem_p.mp h)), if_neg hzp]

/-- **`B_z` on a prime.**  `B_z(p) = -log(p/z)` for `p > z`, and `0` for `p ≤ z`. -/
lemma Bz_apply_prime (z p : ℕ) (hp : Nat.Prime p) (hz : 1 ≤ z) :
    Bz z p = if z < p then -Real.log ((p:ℝ)/(z:ℝ)) else 0 := by
  simpa using Bz_apply_prime_pow z p 1 hp le_rfl hz

/-- **Pointwise form of the mixed sum.**  For `2 ≤ z`, `N < z²` and `n ≤ N`,
`Λ(n) B_z(n) = -log n · log(n/z)` when `n` is a prime `> z`, and `0` otherwise. -/
lemma vonMangoldt_mul_Bz_pointwise (z N n : ℕ) (hz : 2 ≤ z) (hnN : n ≤ N)
    (hN : N < z*z) :
    ArithmeticFunction.vonMangoldt n * Bz z n
      = if (Nat.Prime n ∧ z < n) then -(Real.log (n:ℝ) * Real.log ((n:ℝ)/(z:ℝ))) else 0 := by
  by_cases hP : Nat.Prime n ∧ z < n
  · rw [if_pos hP]
    obtain ⟨hpn, hzn⟩ := hP
    rw [ArithmeticFunction.vonMangoldt_apply_prime hpn, Bz_apply_prime z n hpn (by omega), if_pos hzn]
    ring
  · rw [if_neg hP]
    by_cases hv : ArithmeticFunction.vonMangoldt n = 0
    · rw [hv, zero_mul]
    · have hpp : IsPrimePow n := (ArithmeticFunction.vonMangoldt_ne_zero_iff).mp hv
      rw [isPrimePow_nat_iff] at hpp
      obtain ⟨p, k, hp, hk0, hpk⟩ := hpp
      rw [← hpk, Bz_apply_prime_pow z p k hp (by omega) (by omega)]
      by_cases hzp : z < p
      · exfalso
        have hk1 : k = 1 := by
          by_contra hk1
          have hk2 : 2 ≤ k := by omega
          have hle : p^2 ≤ p^k := Nat.pow_le_pow_right hp.one_le hk2
          have hn_lt : p^k < z*z := by rw [hpk]; exact lt_of_le_of_lt hnN hN
          have hz2 : z*z < p^2 := by nlinarith [hzp]
          omega
        exact hP ⟨by rw [← hpk, hk1, pow_one]; exact hp, by rw [← hpk, hk1, pow_one]; exact hzp⟩
      · rw [if_neg hzp, mul_zero]

/-- **The mixed sum in Graham's case `N < z²`.**  For `2 ≤ z ≤ N < z²`, the only `n ∈ [2,N]`
with `Λ(n) ≠ 0` and `B_z(n) ≠ 0` are the primes `p` with `z < p ≤ N`: if `Λ(n) ≠ 0` then
`n = p^m`, and `B_z(p^m) = -log(p/z)` for `p > z` (terms with `p^j`, `j ≥ 2`, carry `μ = 0`)
while `B_z(p^m) = 0` for `p ≤ z`; and `p > z`, `m ≥ 2` would force `n ≥ p² > z² > N`.
There `Λ(p) B_z(p) = -log p log(p/z)`, whence
`∑_{n ∈ [2,N]} Λ(n) B_z(n) = - ∑_{z < p ≤ N} log p · log(p/z)`. -/
theorem vonMangoldt_mul_Bz_sum (z N : ℕ) (hz : 2 ≤ z) (hzN : z ≤ N) (hN : N < z * z) :
    (∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n * Bz z n)
      = - (∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < p),
            Real.log (p : ℝ) * Real.log ((p : ℝ) / (z : ℝ))) := by
  have hset : (Finset.Icc 2 N).filter (fun n => Nat.Prime n ∧ z < n)
      = (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < p) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h2, hN4⟩, hp, hz'⟩
      exact ⟨⟨by omega, hN4⟩, hp, hz'⟩
    · rintro ⟨⟨h1, hN4⟩, hp, hz'⟩
      exact ⟨⟨hp.two_le, hN4⟩, hp, hz'⟩
  calc ∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n * Bz z n
      = ∑ n ∈ Finset.Icc 2 N, (if (Nat.Prime n ∧ z < n) then
          -(Real.log (n:ℝ) * Real.log ((n:ℝ)/(z:ℝ))) else 0) :=
        Finset.sum_congr rfl (fun n hn => vonMangoldt_mul_Bz_pointwise z N n hz
          (Finset.mem_Icc.mp hn).2 hN)
    _ = ∑ n ∈ (Finset.Icc 2 N).filter (fun n => Nat.Prime n ∧ z < n),
          -(Real.log (n:ℝ) * Real.log ((n:ℝ)/(z:ℝ))) := by
        rw [Finset.sum_filter]
    _ = -∑ n ∈ (Finset.Icc 2 N).filter (fun n => Nat.Prime n ∧ z < n),
          Real.log (n:ℝ) * Real.log ((n:ℝ)/(z:ℝ)) := by rw [Finset.sum_neg_distrib]
    _ = -∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < p),
          Real.log (p:ℝ) * Real.log ((p:ℝ)/(z:ℝ)) := by rw [hset]

end

end Work.LinnikAreas.Density4
