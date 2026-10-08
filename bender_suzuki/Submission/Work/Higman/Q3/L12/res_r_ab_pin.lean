import Mathlib
import Submission.Work.Higman.Q3.L12.case_core

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3.L12

/-- Arithmetic pin (i): a positive multiple of `n` below `2n` equals `n`.
Used to turn the congruence `2r+1 ≡ 0 (mod n)` into the equality `2r+1 = n`. -/
lemma pin_two_r_add_one_eq {n r : ℕ} (hr : r < n)
    (h : 2 * r + 1 ≡ 0 [MOD n]) : 2 * r + 1 = n := by
  have hdvd : n ∣ 2 * r + 1 := Nat.modEq_zero_iff_dvd.mp h
  obtain ⟨c, hc'⟩ := hdvd
  have hc2 : c < 2 := by
    by_contra hge
    push Not at hge
    have hh : n * 2 ≤ n * c := Nat.mul_le_mul_left n hge
    nlinarith
  have hpos : 0 < n * c := by omega
  have hcpos : 0 < c := Nat.pos_of_mul_pos_left hpos
  have hc1 : c = 1 := by omega
  rw [hc1] at hc'
  simpa using hc'

/-- Arithmetic pin (ii): with `1 ≤ r`, the congruence `2r-1 ≡ 0 (mod n)` gives `2r-1 = n`. -/
lemma pin_two_r_sub_one_eq {n r : ℕ} (hr : r < n) (hr0 : r ≠ 0)
    (h : 2 * r - 1 ≡ 0 [MOD n]) : 2 * r - 1 = n := by
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
  have hdvd : n ∣ 2 * r - 1 := Nat.modEq_zero_iff_dvd.mp h
  obtain ⟨c, hc'⟩ := hdvd
  have hc2 : c < 2 := by
    by_contra hge
    push Not at hge
    have hh : n * 2 ≤ n * c := Nat.mul_le_mul_left n hge
    have hlt : 2 * r - 1 < 2 * n := by omega
    nlinarith
  have hpos : 0 < n * c := by omega
  have hcpos : 0 < c := Nat.pos_of_mul_pos_left hpos
  have hc1 : c = 1 := by omega
  rw [hc1] at hc'
  simpa using hc'

/-- The two alternatives `2r+1 ≡ 0` and `2r-1 ≡ 0` mod `n` are mutually exclusive for `n ≥ 2`. -/
lemma pin_two_r_excl {n r : ℕ} (hn : 2 ≤ n)
    (h1 : 2 * r + 1 ≡ 0 [MOD n]) (h2 : 2 * r - 1 ≡ 0 [MOD n]) : False := by
  have hA : 2 * r - 1 ≡ 2 * r + 1 [MOD n] := h2.trans h1.symm
  have hle : 2 * r - 1 ≤ 2 * r + 1 := by omega
  have hdvd : n ∣ (2 * r + 1) - (2 * r - 1) := (Nat.modEq_iff_dvd' hle).mp hA
  have hXpos : 0 < (2 * r + 1) - (2 * r - 1) := by omega
  have hXle : (2 * r + 1) - (2 * r - 1) ≤ 2 := by omega
  have hn2 : n = 2 := le_antisymm (le_trans (Nat.le_of_dvd hXpos hdvd) hXle) hn
  rw [hn2] at h1
  have hdvd2 : 2 ∣ 2 * r + 1 := Nat.modEq_zero_iff_dvd.mp h1
  obtain ⟨c, hc⟩ := hdvd2
  omega

/-- **The pinned `r`/`ab` resonance congruence of Higman's Lemma 12.**

This is the "pinned" strengthening of `res_r_ab` in the situation where only the *support* of
`g` is relevant: since every nonzero entry `g k l` satisfies the same congruence, and the two
alternative resolutions of `res_r_ab` are mutually exclusive for `n ≥ 2`, the support is confined
to a single one of the two patterns and the corresponding integrality condition holds.

Concretely: with `2 ≤ n`, `0 < r < n`, if every nonzero entry of `g` (with `k, l < n`) satisfies
`2 * 2^k + 2^l * (1 + 2^r) ≡ 2 * (1 + 2^r) (mod 2^n - 1)`, and `g` is not identically zero on
`[0,n) × [0,n)`, then either

* `2r + 1 ≡ 0 (mod n)` and *every* nonzero entry has `k = n - 1`, `l = r + 1`, or
* `2r - 1 ≡ 0 (mod n)` and *every* nonzero entry has `k = r - 1`, `l = r`. -/
theorem res_r_ab_pin {n r : ℕ} (hn : 2 ≤ n) (hr : r < n) (hr0 : r ≠ 0)
    {g : ℕ → ℕ → GaloisField 2 n}
    (hres : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 →
        2 * 2 ^ k + 2 ^ l * (1 + 2 ^ r) ≡ 2 * (1 + 2 ^ r) [MOD 2 ^ n - 1])
    (hsupp : ∃ k l : ℕ, k < n ∧ l < n ∧ g k l ≠ 0) :
    (2 * r + 1 ≡ 0 [MOD n] ∧ ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 → k = n - 1 ∧ l = r + 1) ∨
    (2 * r - 1 ≡ 0 [MOD n] ∧ ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 → k = r - 1 ∧ l = r) := by
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
  -- normalise the hypothesis to the argument order expected by `res_r_ab`
  have hres' : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 →
      2 ^ k * 2 + 2 ^ l * (1 + 2 ^ r) ≡ 2 * (1 + 2 ^ r) [MOD 2 ^ n - 1] := by
    intro k l hk hl hgl
    have h := hres k l hk hl hgl
    rw [mul_comm (2 : ℕ) (2 ^ k)] at h
    exact h
  obtain ⟨k0, l0, hk0, hl0, hg0⟩ := hsupp
  rcases res_r_ab hn hr hr0 hr1 hk0 hl0 (hres' k0 l0 hk0 hl0 hg0) with
    ⟨hk1, hc1, hl1⟩ | ⟨hk2, hc2, hl2⟩
  · -- first alternative for the reference point: everything lies on the first pattern
    refine Or.inl ⟨hc1, ?_⟩
    have hrp1 : r + 1 < n := by
      have := pin_two_r_add_one_eq hr hc1
      omega
    intro k l hk hl hgl
    rcases res_r_ab hn hr hr0 hr1 hk hl (hres' k l hk hl hgl) with
      ⟨hk', hc', hl'⟩ | ⟨hk'', hc'', hl''⟩
    · exact ⟨Nat.ModEq.eq_of_lt_of_lt hk' hk (by omega),
        Nat.ModEq.eq_of_lt_of_lt hl' hl hrp1⟩
    · exact (pin_two_r_excl hn hc1 hc'').elim
  · -- second alternative for the reference point
    refine Or.inr ⟨hc2, ?_⟩
    have hrm1 : 2 * r - 1 = n := pin_two_r_sub_one_eq hr hr0 hc2
    have hnr : n + 1 - r = r := by omega
    intro k l hk hl hgl
    rcases res_r_ab hn hr hr0 hr1 hk hl (hres' k l hk hl hgl) with
      ⟨hk', hc', hl'⟩ | ⟨hk'', hc'', hl''⟩
    · exact (pin_two_r_excl hn hc' hc2).elim
    · refine ⟨Nat.ModEq.eq_of_lt_of_lt hk'' hk (by omega), ?_⟩
      have hl3 : l ≡ r [MOD n] := by
        rw [← hnr]
        exact hl''
      exact Nat.ModEq.eq_of_lt_of_lt hl3 hl hr

end Work.Higman.Q3.L12
