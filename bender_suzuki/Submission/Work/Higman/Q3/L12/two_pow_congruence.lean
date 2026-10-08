import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3.L12

/-- Auxiliary: with `0 < r < n`, `k < n`, `l < n`, the residue condition
`2 ^ k + 2 ^ l ≡ 1 + 2 ^ r [MOD 2 ^ n - 1]` forces the plain equality
`2 ^ k + 2 ^ l = 1 + 2 ^ r` (the modulus is large enough to detect the
difference, which lies strictly between `-(2 ^ n - 1)` and `2 ^ n - 1`). -/
theorem two_pow_sum_eq_of_modEq {n r k l : ℕ} (hn : 0 < n)
    (hr : r < n) (hk : k < n) (hl : l < n) (hr0 : r ≠ 0)
    (h : 2 ^ k + 2 ^ l ≡ 1 + 2 ^ r [MOD 2 ^ n - 1]) :
    2 ^ k + 2 ^ l = 1 + 2 ^ r := by
  have hn2 : 2 ≤ n := by omega
  -- `2 ^ (n-1) + 2 ^ (n-1) = 2 ^ n`
  have hpow : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
    have hn1 : (n - 1) + 1 = n := by omega
    calc 2 ^ (n - 1) + 2 ^ (n - 1) = 2 * 2 ^ (n - 1) := by ring
      _ = 2 ^ (n - 1) * 2 := by ring
      _ = 2 ^ ((n - 1) + 1) := (pow_succ 2 (n - 1)).symm
      _ = 2 ^ n := by rw [hn1]
  have hA : 2 ^ k + 2 ^ l ≤ 2 ^ n := by
    have h1 : 2 ^ k ≤ 2 ^ (n - 1) := by
      rw [Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num)]; omega
    have h2 : 2 ^ l ≤ 2 ^ (n - 1) := by
      rw [Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num)]; omega
    linarith
  have hB : 1 + 2 ^ r ≤ 2 ^ n - 1 := by
    have h1 : 2 ^ r ≤ 2 ^ (n - 1) := by
      rw [Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num)]; omega
    have h2 : 2 ≤ 2 ^ (n - 1) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 1) := by
              rw [Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num)]; omega
    have h4 : 2 ^ r + 1 < 2 ^ n := by linarith
    omega
  have hcast : ((2 ^ n - 1 : ℕ) : ℤ) = (2 : ℤ) ^ n - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  set d : ℤ := ((1 + 2 ^ r : ℕ) : ℤ) - ((2 ^ k + 2 ^ l : ℕ) : ℤ) with hd
  have hdvd : (2 : ℤ) ^ n - 1 ∣ d := by
    have := h.dvd
    rw [hcast] at this
    simpa [hd] using this
  have hle : d ≤ (2 : ℤ) ^ n - 1 - 2 := by
    have h1 : ((1 + 2 ^ r : ℕ) : ℤ) ≤ (2 : ℤ) ^ n - 1 := by
      rw [← hcast]; exact_mod_cast hB
    have h2 : (2 : ℤ) ≤ ((2 ^ k + 2 ^ l : ℕ) : ℤ) := by
      have : 2 ≤ 2 ^ k + 2 ^ l := by
        have a := Nat.one_le_two_pow (n := k)
        have b := Nat.one_le_two_pow (n := l)
        omega
      exact_mod_cast this
    linarith [hd]
  have hge : 2 - (2 : ℤ) ^ n ≤ d := by
    have h2 : ((2 ^ k + 2 ^ l : ℕ) : ℤ) ≤ (2 : ℤ) ^ n := by
      have hh := hA
      push_cast
      exact_mod_cast hh
    have h1 : (2 : ℤ) ≤ ((1 + 2 ^ r : ℕ) : ℤ) := by
      have : 2 ≤ 1 + 2 ^ r := by
        have a := Nat.one_le_two_pow (n := r)
        omega
      exact_mod_cast this
    linarith [hd]
  have hpow2 : (1 : ℤ) < (2 : ℤ) ^ n := by
    have : (1 : ℤ) < 2 ^ 2 := by norm_num
    exact lt_of_lt_of_le this (pow_le_pow_right₀ (by norm_num) hn2)
  have habs : |d| < (2 : ℤ) ^ n - 1 := by
    rw [abs_lt]
    constructor <;> linarith [hle, hge, hpow2]
  have hzero : d = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have : ((2 ^ k + 2 ^ l : ℕ) : ℤ) = ((1 + 2 ^ r : ℕ) : ℤ) := by linarith [hd, hzero]
  exact_mod_cast this

/-- **The two-term congruence** (the `B` case of Higman's Lemma 12).

If `2 ^ k + 2 ^ l ≡ 2 ^ 0 + 2 ^ r (mod 2 ^ n - 1)` with `0 < r < n` and `k, l < n`, then
`{k, l} = {0, r}`.

Used as follows: in the `B(n,θ,ε)` case of Lemma 12 (`θ = α ↦ α^{2^r}`) the two constituents `U`,
`U'` have the same eigenvalue `ν = ν'` and satisfy `ν ^ (1 + 2 ^ r) = λ`; the resonance condition
`e k l ≠ 0 ⟹ ν ^ (2 ^ k) ν' ^ (2 ^ l) = λ` then reads `2 ^ k + 2 ^ l ≡ 1 + 2 ^ r (mod 2 ^ n - 1)`,
so the only non-zero cross terms of the pinned squaring form are `e 0 r` and `e r 0`.

Exhaustively verified for `n ≤ 79`.  Proof: put `u = 2 ^ k + 2 ^ l - 1 - 2 ^ r`; then
`-(2 ^ n - 1) < u < 2 ^ n - 1`, so `u = 0` or `u = 2 ^ n - 1`; the second case would give
`2 ^ k + 2 ^ l = 2 ^ n + 2 ^ r > 2 ^ n`, impossible for `k, l < n`, so `u = 0` and uniqueness of
the binary expansion forces `{k, l} = {0, r}` (the case `k = l` would need `2 ^ (k+1) = 1 + 2 ^ r`,
i.e. `k = r = 0`, excluded by `hr0`). -/
theorem two_pow_congruence {n r k l : ℕ} (hn : 0 < n)
    (hr : r < n) (hk : k < n) (hl : l < n) (hr0 : r ≠ 0)
    (h : 2 ^ k + 2 ^ l ≡ 2 ^ 0 + 2 ^ r [MOD 2 ^ n - 1]) :
    (k = 0 ∧ l = r) ∨ (k = r ∧ l = 0) := by
  have h' : 2 ^ k + 2 ^ l ≡ 1 + 2 ^ r [MOD 2 ^ n - 1] := by simpa using h
  have heq : 2 ^ k + 2 ^ l = 1 + 2 ^ r := two_pow_sum_eq_of_modEq hn hr hk hl hr0 h'
  -- `1 + 2 ^ r` is odd, since `r ≠ 0`
  have heven : Even (2 ^ r) := by
    rw [Nat.even_pow]; exact ⟨even_two, hr0⟩
  have hodd : Odd (2 ^ k + 2 ^ l) := by
    rw [heq]; exact Odd.add_even odd_one heven
  -- hence `2 ^ k + 2 ^ l` is odd, so `k = 0` or `l = 0`
  have hnotboth : ¬ (0 < k ∧ 0 < l) := by
    rintro ⟨hkp, hlp⟩
    have hk2 : Even (2 ^ k) := by rw [Nat.even_pow]; exact ⟨even_two, by omega⟩
    have hl2 : Even (2 ^ l) := by rw [Nat.even_pow]; exact ⟨even_two, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hodd) (hk2.add hl2)
  rcases Nat.eq_zero_or_pos k with hk0 | hkp
  · left
    refine ⟨hk0, ?_⟩
    rw [hk0, pow_zero] at heq
    have : 2 ^ l = 2 ^ r := by omega
    exact Nat.pow_right_injective (le_refl 2) this
  · right
    have hl0 : l = 0 := by
      by_contra hl0
      exact hnotboth ⟨hkp, Nat.pos_of_ne_zero hl0⟩
    refine ⟨?_, hl0⟩
    rw [hl0, pow_zero] at heq
    have : 2 ^ k = 2 ^ r := by omega
    exact Nat.pow_right_injective (le_refl 2) this

end Work.Higman.Q3.L12
