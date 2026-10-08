import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

/-- Arithmetic core of the 2-adic bookkeeping for `twoAdic_core`.

If `A, B, C` are the exponents of `2` in `t - 1`, `t + 1`, `s` respectively, then the four
hypotheses of `twoAdic_core` translate into the inequalities below, and the conclusion becomes
`m ≤ B ∧ m - 1 ≤ C ∧ C < m`.  The key point is that `min A B = 1` (the two consecutive even
numbers `t - 1`, `t + 1` have exactly one factor of `2` between them). -/
lemma twoAdic_arith {A B C m : ℕ} (hm : 2 ≤ m) (_hA1 : 1 ≤ A) (_hB1 : 1 ≤ B)
    (hmin : min A B = 1) (hab : m ≤ A + B) (hac : m ≤ A + C) (hAm : A < m)
    (hC : C < min B m) : m ≤ B ∧ m - 1 ≤ C ∧ C < m := by
  omega

theorem twoAdic_core {m t s : ℕ} (hm : 2 ≤ m) (ht : t % 2 = 1)
    (h1 : 2 ^ m ∣ (t - 1) * (t + 1)) (h2 : 2 ^ m ∣ (t - 1) * s)
    (h3 : ¬ (2 ^ m ∣ (t - 1))) (h4 : ¬ (Nat.gcd (t + 1) (2 ^ m) ∣ s)) :
    2 ^ m ∣ (t + 1) ∧ 2 ^ (m - 1) ∣ s ∧ ¬ (2 ^ m ∣ s) := by
  have hodd : Odd t := Nat.odd_iff.mpr ht
  -- `t` is odd, so `2 ∣ t - 1` and `2 ∣ t + 1`.
  have h2sub : 2 ∣ t - 1 := even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one)
  have h2add : 2 ∣ t + 1 := even_iff_two_dvd.mp (Odd.add_odd hodd odd_one)
  -- Nonvanishing of the numbers whose 2-adic valuations occur.
  have ht_ne_one : t ≠ 1 := by
    rintro rfl
    exact h3 (dvd_zero _)
  have ht1 : t - 1 ≠ 0 := by omega
  have ht2 : t + 1 ≠ 0 := by omega
  have hs : s ≠ 0 := by rintro rfl; exact h4 (dvd_zero _)
  -- Both `t - 1` and `t + 1` have 2-adic valuation at least one.
  have hA1 : 1 ≤ padicValNat 2 (t - 1) := (padicValNat_dvd_iff_le ht1).mp (by simpa using h2sub)
  have hB1 : 1 ≤ padicValNat 2 (t + 1) := (padicValNat_dvd_iff_le ht2).mp (by simpa using h2add)
  -- Consecutive even numbers `t - 1`, `t + 1` cannot both be divisible by `4`.
  have hmin : min (padicValNat 2 (t - 1)) (padicValNat 2 (t + 1)) = 1 := by
    have hle1 : min (padicValNat 2 (t - 1)) (padicValNat 2 (t + 1)) ≤ 1 := by
      by_contra hcon
      have hA2 : 2 ≤ padicValNat 2 (t - 1) := by omega
      have hB2 : 2 ≤ padicValNat 2 (t + 1) := by omega
      have hd1 : 2 ^ 2 ∣ t - 1 := (padicValNat_dvd_iff_le ht1).mpr hA2
      have hd2 : 2 ^ 2 ∣ t + 1 := (padicValNat_dvd_iff_le ht2).mpr hB2
      have hd : 2 ^ 2 ∣ 2 := by
        have hh := Nat.dvd_sub hd2 hd1
        have hsub : (t + 1) - (t - 1) = 2 := by omega
        rwa [hsub] at hh
      exact absurd hd (by norm_num)
    omega
  -- Valuation inequalities coming from the four hypotheses.
  have hab : m ≤ padicValNat 2 (t - 1) + padicValNat 2 (t + 1) := by
    have hneq : (t - 1) * (t + 1) ≠ 0 := Nat.mul_ne_zero ht1 ht2
    have h := (padicValNat_dvd_iff_le hneq).mp h1
    rwa [padicValNat.mul ht1 ht2] at h
  have hac : m ≤ padicValNat 2 (t - 1) + padicValNat 2 s := by
    have hneq : (t - 1) * s ≠ 0 := Nat.mul_ne_zero ht1 hs
    have h := (padicValNat_dvd_iff_le hneq).mp h2
    rwa [padicValNat.mul ht1 hs] at h
  have hAm : padicValNat 2 (t - 1) < m := by
    rw [padicValNat_dvd_iff_le ht1] at h3
    exact Nat.lt_of_not_le h3
  -- `h4` controls the valuation of `s`: writing `gcd (t + 1) (2 ^ m) = 2 ^ k` with `k ≤ m`,
  -- the hypothesis says `2 ^ k ∤ s`, i.e. `padicValNat 2 s < k ≤ min (padicValNat 2 (t + 1)) m`.
  have hC : padicValNat 2 s < min (padicValNat 2 (t + 1)) m := by
    obtain ⟨k, _hk_le, hk_eq⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_right (t + 1) (2 ^ m))
    have hk_dvd : 2 ^ k ∣ t + 1 := by rw [← hk_eq]; exact Nat.gcd_dvd_left _ _
    have hkB : k ≤ padicValNat 2 (t + 1) := (padicValNat_dvd_iff_le ht2).mp hk_dvd
    have hnot : ¬ 2 ^ k ∣ s := by rw [← hk_eq]; exact h4
    have hCk : padicValNat 2 s < k := by
      rw [padicValNat_dvd_iff_le hs] at hnot
      exact Nat.lt_of_not_le hnot
    omega
  -- Combine the valuation facts and translate back into divisibility statements.
  obtain ⟨hmB, hmC, hCm⟩ := twoAdic_arith hm hA1 hB1 hmin hab hac hAm hC
  exact ⟨(padicValNat_dvd_iff_le ht2).mpr hmB, (padicValNat_dvd_iff_le hs).mpr hmC,
    fun h => absurd ((padicValNat_dvd_iff_le hs).mp h) (not_le.mpr hCm)⟩

end Work.BrauerSuzuki.Quaternion
