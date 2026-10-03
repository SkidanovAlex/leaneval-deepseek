import Mathlib
import Submission.Work.FIArea2.TsumDefs

/-!
# `Work.FIArea2.stratum_count_bound`

The counting lemma behind the "strata" of the §6 congruence system: for `ν ≥ 1`, `k < (ν+1)/2`
and `a` odd, if `2^k ∣ h₂` and, among the `r < 2^{ν-2k}`, some `r` satisfies both

* `2^{ν-2k} ∣ r² - a` and
* `2^{ν-k-1} ∣ h₁ + r h₂`,

then (with `2^ν ∤ h₁² - a h₂²`) necessarily

* `2^{ν-1} ∣ h₁² - a h₂²`, and
* there is **at most one** such `r`.

The proof is elementary `2`-adic bookkeeping.  Writing `t = h₁ + r h₂` (so `2^M ∣ t` with
`M = ν-k-1`) and `s = h₁ - r h₂ = t - 2 r h₂`, the hypothesis `2^k ∣ h₂` gives `2^{k+1} ∣ 2 r h₂`,
hence `2^k ∣ s`; the identity

  `h₁² - a h₂² = s·t + h₂²·(r² - a)`

then exhibits `h₁² - a h₂²` as a sum of a multiple of `2^{k+M} = 2^{ν-1}` and of a multiple of
`2^{2k+N} = 2^ν`.  When moreover `N = ν-2k ≥ 2` one has `M ≥ k+1`, so in fact `2^{k+1} ∣ s` and
`2^ν ∣ h₁² - a h₂²`, contradicting `hnot`; the remaining case is `N = 1`, where `r` is forced to be
`1` because `a` is odd.
-/

namespace Work.FIArea2

open Finset

/-- **The `2`-adic core.**  Given a single solution `r` of the two congruences, the quantity
`h₁² - a h₂²` is divisible by `2^L` whenever `L ≤ m + M` and `L ≤ 2k + N`, where `m ≤ M` and
`m ≤ k+1` measure how many powers of `2` the pair `(h₁ - r h₂, h₁ + r h₂)` is known to carry. -/
private lemma dvd_of_solution (k N M m L : ℕ) (a h1 h2 r : ℤ)
    (hd2 : (2:ℤ)^k ∣ h2) (hdr : (2:ℤ)^N ∣ r^2 - a) (hdt : (2:ℤ)^M ∣ h1 + r*h2)
    (hmM : m ≤ M) (hmk : m ≤ k+1) (hL1 : L ≤ m + M) (hL2 : L ≤ 2*k + N) :
    (2:ℤ)^L ∣ h1^2 - a*h2^2 := by
  -- `2^m ∣ h₁ + r h₂`
  have hm_t : (2:ℤ)^m ∣ h1 + r*h2 := dvd_trans (pow_dvd_pow (2:ℤ) hmM) hdt
  -- `2^{k+1} ∣ 2 h₂`
  have hk1 : (2:ℤ)^(k+1) ∣ 2*h2 := by
    have h := mul_dvd_mul (dvd_refl (2:ℤ)) hd2
    simpa [pow_succ'] using h
  -- `2^{k+1} ∣ 2 (r h₂)`
  have hk1r : (2:ℤ)^(k+1) ∣ 2*(r*h2) := by
    have h : (2:ℤ)^(k+1) ∣ (2*h2)*r := dvd_mul_of_dvd_left hk1 r
    have he : (2*h2)*r = 2*(r*h2) := by ring
    rwa [he] at h
  have hm_r : (2:ℤ)^m ∣ 2*(r*h2) := dvd_trans (pow_dvd_pow (2:ℤ) hmk) hk1r
  -- `2^m ∣ h₁ - r h₂ = (h₁ + r h₂) - 2 (r h₂)`
  have hm_s : (2:ℤ)^m ∣ h1 - r*h2 := by
    have h' : (2:ℤ)^m ∣ (h1 + r*h2) - 2*(r*h2) := Int.dvd_sub hm_t hm_r
    have he : (h1 + r*h2) - 2*(r*h2) = h1 - r*h2 := by ring
    rwa [he] at h'
  -- first summand of the identity
  have hst : (2:ℤ)^(m+M) ∣ (h1 - r*h2)*(h1 + r*h2) := by
    have h := mul_dvd_mul hm_s hdt
    rwa [← pow_add] at h
  -- second summand of the identity
  have hcross : (2:ℤ)^(2*k+N) ∣ h2^2 * (r^2 - a) := by
    have h2k : (2:ℤ)^(2*k) ∣ h2^2 := by
      have h := mul_dvd_mul hd2 hd2
      rw [← pow_add] at h
      simpa [two_mul, pow_two] using h
    have h := mul_dvd_mul h2k hdr
    rwa [← pow_add] at h
  have e1 : (2:ℤ)^L ∣ (h1 - r*h2)*(h1 + r*h2) := dvd_trans (pow_dvd_pow (2:ℤ) hL1) hst
  have e2 : (2:ℤ)^L ∣ h2^2 * (r^2 - a) := dvd_trans (pow_dvd_pow (2:ℤ) hL2) hcross
  have hh := Int.dvd_add e1 e2
  convert hh using 1
  ring

theorem stratum_count_bound (ν k : ℕ) (hν : 1 ≤ ν) (hk : k < (ν + 1) / 2) (a h1 h2 : ℤ) (ha : Odd a)
    (h2dvd : ((2 ^ k : ℕ) : ℤ) ∣ h2)
    (hnot : ¬ (((2 ^ ν : ℕ) : ℤ) ∣ h1 ^ 2 - a * h2 ^ 2))
    (hcard : 0 < ((Finset.range (2 ^ (ν - 2 * k))).filter
        (fun r : ℕ => ((2 ^ (ν - 2 * k) : ℕ) : ℤ) ∣ (r : ℤ) ^ 2 - a ∧
          ((2 ^ (ν - k - 1) : ℕ) : ℤ) ∣ h1 + (r : ℤ) * h2)).card) :
    (((2 ^ (ν - 1) : ℕ) : ℤ) ∣ h1 ^ 2 - a * h2 ^ 2) ∧
      ((Finset.range (2 ^ (ν - 2 * k))).filter
        (fun r : ℕ => ((2 ^ (ν - 2 * k) : ℕ) : ℤ) ∣ (r : ℤ) ^ 2 - a ∧
          ((2 ^ (ν - k - 1) : ℕ) : ℤ) ∣ h1 + (r : ℤ) * h2)).card ≤ 1 := by
  -- extract a solution from the positive count
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hcard
  rw [Finset.mem_filter, Finset.mem_range] at hr
  obtain ⟨hrlt, hr1, hr2⟩ := hr
  -- rewrite the ℕ-casts into powers of `(2 : ℤ)`
  have hd2 : (2:ℤ)^k ∣ h2 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h2dvd
  have hdr : (2:ℤ)^(ν - 2*k) ∣ (r:ℤ)^2 - a := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hr1
  have hdt : (2:ℤ)^(ν - k - 1) ∣ h1 + (r:ℤ)*h2 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hr2
  have hnot' : ¬ ((2:ℤ)^ν ∣ h1^2 - a*h2^2) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hnot
  have hNpos : 1 ≤ ν - 2*k := by omega
  -- first conclusion: `2^{ν-1} ∣ h₁² - a h₂²`
  have key1 : (2:ℤ)^(ν-1) ∣ h1^2 - a*h2^2 :=
    dvd_of_solution k (ν-2*k) (ν-k-1) k (ν-1) a h1 h2 (r:ℤ) hd2 hdr hdt
      (by omega) (by omega) (by omega) (by omega)
  by_cases hN2 : 2 ≤ ν - 2*k
  · -- `N ≥ 2`: then `2^ν ∣ h₁² - a h₂²`, contradicting `hnot`; the count bound follows vacuously
    have key2 : (2:ℤ)^ν ∣ h1^2 - a*h2^2 :=
      dvd_of_solution k (ν-2*k) (ν-k-1) (k+1) ν a h1 h2 (r:ℤ) hd2 hdr hdt
        (by omega) (by omega) (by omega) (by omega)
    exact (hnot' key2).elim
  · -- `N = 1`: the remaining case `r < 2` with `a` odd forces `r = 1`
    have hN1 : ν - 2*k = 1 := by omega
    refine ⟨?_, ?_⟩
    · simpa only [Nat.cast_pow, Nat.cast_ofNat] using key1
    · rw [Finset.card_le_one]
      intro x hx y hy
      rw [Finset.mem_filter, Finset.mem_range] at hx hy
      have hx1 : x = 1 := by
        have hpd : (2:ℤ) ∣ (x:ℤ)^2 - a := by
          simpa only [hN1, pow_one, Nat.cast_ofNat] using hx.2.1
        have hxlt : x < 2 := by
          simpa only [hN1, pow_one] using hx.1
        have hnot2 : ¬ ((2:ℤ) ∣ a) := by
          rintro ⟨c, hc⟩
          obtain ⟨m, hm⟩ := ha
          omega
        have hxne : x ≠ 0 := by
          rintro rfl
          simp only [Nat.cast_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_sub] at hpd
          exact hnot2 (dvd_neg.mp hpd)
        omega
      have hy1 : y = 1 := by
        have hpd : (2:ℤ) ∣ (y:ℤ)^2 - a := by
          simpa only [hN1, pow_one, Nat.cast_ofNat] using hy.2.1
        have hylt : y < 2 := by
          simpa only [hN1, pow_one] using hy.1
        have hnot2 : ¬ ((2:ℤ) ∣ a) := by
          rintro ⟨c, hc⟩
          obtain ⟨m, hm⟩ := ha
          omega
        have hyne : y ≠ 0 := by
          rintro rfl
          simp only [Nat.cast_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_sub] at hpd
          exact hnot2 (dvd_neg.mp hpd)
        omega
      rw [hx1, hy1]

end Work.FIArea2
