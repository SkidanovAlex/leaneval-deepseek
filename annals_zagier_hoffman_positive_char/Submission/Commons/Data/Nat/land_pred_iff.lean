import Mathlib.Data.Nat.Factorization.Basic

namespace Commons.Data.Nat

/-- Factorisation of the "no carry" condition `j &&& (k - 1) = 0` (equivalently: `j` and `k-1`
added in base 2 without carry, i.e. `(j + (k-1)).choose j` odd) along the exact power of two
dividing `k`:

`j &&& (k - 1) = 0 ↔ 2 ^ v_2(k) ∣ j ∧ (j / 2 ^ v_2 k) &&& (k / 2 ^ v_2 k - 1) = 0`.

Equivalently: `j` is admissible iff `j = 2 ^ v_2 k * u` where `u` is bitwise disjoint from
`k / 2 ^ v_2 k - 1`. In particular the least admissible `j ≥ 1` is `2 ^ v_2 k`.

Proof strategy: put `a = k.factorization 2` and `m = k / 2 ^ a` (so `2 ^ a ∣ k`, `m` odd,
`k = 2 ^ a * m`).  Then `k - 1 = 2 ^ a * (m - 1) + (2 ^ a - 1)`, so the bits of `k - 1` at
positions `< a` are all `1` and its bits at positions `≥ a` are those of `m - 1`
(`Nat.add_mul_div_left`, `Nat.div_eq_of_lt`, `Nat.Prime.pow_dvd_iff_le_factorization`,
`Nat.factorization_eq_zero_iff`, `Nat.not_even_iff_odd`).  Hence `j &&& (k-1) = 0` iff
`2 ^ a ∣ j` (the low bits of `j` vanish) and the shifted high bits of `j` are disjoint from
those of `m - 1`.  Use the bitwise API `Nat.land_comm`, `Nat.land_assoc`, `Nat.testBit_land`,
`Nat.eq_of_testBit_eq`, `Nat.testBit_mul_two_pow`/`Nat.div_two_pow` style lemmas for the
shifting step. -/
theorem land_pred_iff (k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    (j &&& (k - 1) = 0) ↔
      2 ^ k.factorization 2 ∣ j ∧
        (j / 2 ^ k.factorization 2) &&& (k / 2 ^ k.factorization 2 - 1) = 0 := by
  set a := k.factorization 2 with ha
  set m := k / 2 ^ a with hm
  have hk0 : k ≠ 0 := by omega
  -- `2 ^ a ∣ k` since `a = k.factorization 2` is the exact exponent of `2` in `k`.
  have h2a_dvd : 2 ^ a ∣ k := by
    rw [ha]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hk0).mpr le_rfl
  -- `k = 2 ^ a * m`.
  have hk_eq : k = 2 ^ a * m := by
    rw [hm]
    exact (Nat.mul_div_cancel' h2a_dvd).symm
  have hm1 : 1 ≤ m := by
    have hpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, Nat.mul_zero] at hk_eq; omega
      · exact h
    omega
  have h2a_le_k : 2 ^ a ≤ k := by
    rw [hk_eq]
    calc 2 ^ a = 2 ^ a * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ a * m := Nat.mul_le_mul_left _ hm1
  -- `k - 1 = 2 ^ a * (m - 1) + (2 ^ a - 1)`.
  have hpred : k - 1 = 2 ^ a * (m - 1) + (2 ^ a - 1) := by
    have h1 : 2 ^ a * (m - 1) = k - 2 ^ a := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← hk_eq]
    rw [h1, ← Nat.add_sub_assoc (Nat.one_le_two_pow (n := a)), Nat.sub_add_cancel h2a_le_k]
  -- low bits of `k - 1` are all `1`
  have hmod : (k - 1) % 2 ^ a = 2 ^ a - 1 := by
    rw [hpred, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos a) Nat.zero_lt_one)]
  -- high bits of `k - 1` are those of `m - 1`
  have hdiv : (k - 1) / 2 ^ a = m - 1 := by
    rw [hpred, Nat.mul_add_div (Nat.two_pow_pos a),
      Nat.div_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos a) Nat.zero_lt_one), Nat.add_zero]
  -- `n = 0` in terms of its low and high parts
  have hdecomp : j &&& (k - 1) = 0 ↔
      (j &&& (k - 1)) / 2 ^ a = 0 ∧ (j &&& (k - 1)) % 2 ^ a = 0 := by
    constructor
    · intro h; rw [h]; simp
    · rintro ⟨h1, h2⟩
      have hd := Nat.div_add_mod (j &&& (k - 1)) (2 ^ a)
      rw [h1, h2] at hd
      simpa using hd.symm
  have e1 : (j &&& (k - 1)) % 2 ^ a = j % 2 ^ a := by
    rw [Nat.and_mod_two_pow, hmod,
      Nat.and_two_pow_sub_one_of_lt_two_pow (Nat.mod_lt j (Nat.two_pow_pos a))]
  have e2 : (j &&& (k - 1)) / 2 ^ a = (j / 2 ^ a) &&& (m - 1) := by
    rw [Nat.and_div_two_pow, hdiv]
  rw [hdecomp, e1, e2, Nat.dvd_iff_mod_eq_zero]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2, h1⟩

end Commons.Data.Nat