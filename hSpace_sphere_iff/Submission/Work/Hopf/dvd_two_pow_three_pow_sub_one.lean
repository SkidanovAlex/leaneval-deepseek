import Mathlib

namespace Work.Hopf

/-- For `m ≥ 5`, `4 * m < 2 ^ m`. This is the arithmetic fact used to bound `n`. -/
lemma four_mul_lt_two_pow (m : ℕ) (hm : 5 ≤ m) : 4 * m < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 4 * (m + 1) = 4 * m + 4 := by ring
      _ < 2 ^ m + 2 ^ m := by omega
      _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

/-- For odd `n`, `3 ^ n - 1` is not divisible by `4` (indeed `3 ^ n ≡ 3 [MOD 4]`). -/
lemma odd_three_pow_not_dvd_four (n : ℕ) (hn : Odd n) : ¬ 4 ∣ 3 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  intro h4
  have h1 : 3 ^ (2 * k + 1) ≡ 3 [MOD 4] := by
    have h9 : (9 : ℕ) ≡ 1 [MOD 4] := by norm_num [Nat.ModEq]
    have hk : 9 ^ k ≡ 1 [MOD 4] := by simpa using h9.pow k
    calc 3 ^ (2 * k + 1) = 9 ^ k * 3 := by rw [pow_succ, pow_mul]; norm_num
      _ ≡ 1 * 3 [MOD 4] := hk.mul_right 3
      _ = 3 := by norm_num
  have h2 : 3 ^ (2 * k + 1) - 1 ≡ 2 [MOD 4] := by
    have h1x : 1 ≤ 3 ^ (2 * k + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hs := Nat.ModEq.sub (n := 4) h1x (by norm_num : 1 ≤ (3:ℕ)) h1
      (Nat.ModEq.refl (n := 4) 1)
    simpa using hs
  have hzero : 3 ^ (2 * k + 1) - 1 ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr h4
  have hcon : 2 ≡ 0 [MOD 4] := h2.symm.trans hzero
  rw [Nat.modEq_zero_iff_dvd] at hcon
  norm_num at hcon

theorem dvd_two_pow_three_pow_sub_one (n : ℕ) (hn : 1 ≤ n) (h : (2 : ℕ) ^ n ∣ 3 ^ n - 1) :
    n = 1 ∨ n = 2 ∨ n = 4 := by
  have hne : 3 ^ n - 1 ≠ 0 := by
    have : 2 ≤ 3 ^ n := by
      calc 2 ≤ 3 := by norm_num
        _ = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  -- The `2`-adic valuation of `3 ^ n - 1` is at most `v₂(n) + 2`.
  have hbound : n ≤ padicValNat 2 n + 2 := by
    have hle := (padicValNat_dvd_iff_le (p := 2) (a := 3 ^ n - 1) (n := n) hne).mp h
    rcases Nat.even_or_odd n with he | ho
    · -- LTE: for even `n`, `v₂(3 ^ n - 1) = v₂(n) + 2`.
      have hf := padicValNat.pow_two_sub_one (x := 3) (n := n) (by norm_num)
        (by norm_num) (by omega) he
      have h4 : padicValNat 2 (3 + 1) = 2 := by simpa using padicValNat.prime_pow (p := 2) 2
      have h2 : padicValNat 2 (3 - 1) = 1 := by simp
      rw [h4, h2] at hf
      omega
    · -- For odd `n`, `v₂(3 ^ n - 1) = 1`.
      have hno4 : ¬ 4 ∣ 3 ^ n - 1 := odd_three_pow_not_dvd_four n ho
      have hsmall : ¬ 2 ≤ padicValNat 2 (3 ^ n - 1) := by
        intro hc
        have : (2:ℕ) ^ 2 ∣ 3 ^ n - 1 :=
          (padicValNat_dvd_iff_le (p := 2) (a := 3 ^ n - 1) (n := 2) hne).mpr hc
        exact hno4 (by simpa using this)
      omega
  -- Since `2 ^ v₂(n) ∣ n`, this forces `2 ^ n ≤ 4 * n`.
  have hpow4n : 2 ^ n ≤ 4 * n := by
    have hdvd : 2 ^ padicValNat 2 n ∣ n :=
      (padicValNat_dvd_iff_le (p := 2) (a := n) (n := padicValNat 2 n) (by omega)).mpr le_rfl
    have hle2 : 2 ^ padicValNat 2 n ≤ n := Nat.le_of_dvd (by omega) hdvd
    calc 2 ^ n ≤ 2 ^ (padicValNat 2 n + 2) := Nat.pow_le_pow_right (by norm_num) hbound
      _ = 2 ^ padicValNat 2 n * 2 ^ 2 := by rw [pow_add]
      _ ≤ n * 4 := Nat.mul_le_mul hle2 (le_refl _)
      _ = 4 * n := by ring
  have hn4 : n ≤ 4 := by
    by_contra hc
    have h5 : 5 ≤ n := by omega
    have hlt := four_mul_lt_two_pow n h5
    omega
  -- `n = 3` is excluded by the valuation bound.
  have hn3 : n ≠ 3 := by
    intro h3
    subst h3
    have : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    omega
  omega

end Work.Hopf
