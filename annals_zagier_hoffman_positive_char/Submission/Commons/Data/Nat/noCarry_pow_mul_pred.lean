import Mathlib

namespace Commons.Data.Nat

private lemma div_mul_sub_one {b Y : ℕ} (hb : 0 < b) (hY : 1 ≤ Y) :
    (b * Y - 1) / b = Y - 1 := by
  have hYpos : 0 < Y := by omega
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_sub_right_distrib, one_mul, Nat.mul_comm b Y]
    omega
  · rw [Nat.sub_add_cancel hY, Nat.mul_comm b Y]
    exact Nat.sub_one_lt (Nat.mul_ne_zero (by omega) (by omega))

private lemma pred_mul_add_pred_mod_lt {q x : ℕ} (_hq : 2 ≤ q) (hx : 1 ≤ x) (hxq : x ≤ q) :
    ((q - 1) * x) % q + (x - 1) % q < q := by
  have hxq1 : x - 1 < q := by omega
  have hb : (x - 1) % q = x - 1 := Nat.mod_eq_of_lt hxq1
  have hqx : q - x < q := by omega
  have hle : q ≤ x * q := Nat.le_mul_of_pos_left q (by omega : 0 < x)
  have hmodeq : (q - 1) * x = (q - x) + (x - 1) * q := by
    rw [Nat.mul_sub_right_distrib, Nat.mul_sub_right_distrib, one_mul, one_mul, Nat.mul_comm q x]
    omega
  have ha : (q - 1) * x % q = q - x := by
    rw [hmodeq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hqx]
  rw [ha, hb]
  omega

private lemma pow_mul_mod_self_eq_zero {q a u : ℕ} (_hq : 0 < q) (hu : 1 ≤ u) :
    (q ^ u * a) % q = 0 := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  rw [pow_succ]
  rw [show q ^ v * q * a = q * (q ^ v * a) by ring]
  rw [Nat.mul_mod_right]

private lemma pow_mul_pred_mod {q x u : ℕ} (hq : 2 ≤ q) (hx : 1 ≤ x) (hu : 1 ≤ u) :
    (q ^ u * x - 1) % q = q - 1 := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  rw [pow_succ]
  set Y := q ^ v * x with hYdef
  have hY : 1 ≤ Y := by
    have h1 : 1 ≤ q ^ v := Nat.one_le_pow v q (by omega)
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hdecomp : q ^ v * q * x - 1 = (q - 1) + (Y - 1) * q := by
    have hYeq : q ^ v * q * x = q * Y := by rw [hYdef]; ring
    rw [hYeq]
    rw [show (Y - 1) * q = Y * q - q by rw [Nat.mul_sub_right_distrib, one_mul]]
    rw [Nat.mul_comm q Y]
    have hAq : q ≤ Y * q := Nat.le_mul_of_pos_left q (by omega : 0 < Y)
    omega
  rw [hdecomp, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : q - 1 < q)]

theorem noCarry_pow_mul_pred {q x i j : ℕ} (hq : 2 ≤ q) (hx : 1 ≤ x) (hxq : x ≤ q) :
    q ^ i * ((q - 1) * x) / q ^ j % q + (q ^ i * x - 1) / q ^ j % q < q := by
  have hq0 : 0 < q := by omega
  rcases Nat.lt_or_ge i j with hj | hj
  · have hlt : q ^ i * x - 1 < q ^ j := by
      have h1 : q ^ i * x ≤ q ^ (i + 1) := by
        calc q ^ i * x ≤ q ^ i * q := Nat.mul_le_mul_left _ hxq
          _ = q ^ (i + 1) := by rw [pow_succ]
      have h2 : q ^ (i + 1) ≤ q ^ j := Nat.pow_le_pow_right hq0 (by omega)
      have hxpos : 1 ≤ q ^ i * x := by
        have h1' : 1 ≤ q ^ i := Nat.one_le_pow i q hq0
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      omega
    have hterm2 : (q ^ i * x - 1) / q ^ j = 0 := Nat.div_eq_of_lt hlt
    rw [hterm2, Nat.zero_mod, add_zero]
    exact Nat.mod_lt _ hq0
  · have hi : (i - j) + j = i := Nat.sub_add_cancel hj
    have hqj : 0 < q ^ j := pow_pos hq0 j
    have hpow : q ^ i = q ^ (i - j) * q ^ j := by
      conv_lhs => rw [← hi]
      rw [pow_add]
    have hY : 1 ≤ q ^ (i - j) * x := by
      have h1 : 1 ≤ q ^ (i - j) := Nat.one_le_pow (i - j) q hq0
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hterm1 : q ^ i * ((q - 1) * x) / q ^ j = q ^ (i - j) * ((q - 1) * x) := by
      rw [hpow]
      rw [show q ^ (i - j) * q ^ j * ((q - 1) * x) = q ^ j * (q ^ (i - j) * ((q - 1) * x)) by ring]
      rw [Nat.mul_div_right _ hqj]
    have hterm2 : (q ^ i * x - 1) / q ^ j = q ^ (i - j) * x - 1 := by
      rw [hpow]
      rw [show q ^ (i - j) * q ^ j * x = q ^ j * (q ^ (i - j) * x) by ring]
      rw [div_mul_sub_one hqj hY]
    rw [hterm1, hterm2]
    rcases Nat.eq_zero_or_pos (i - j) with h0 | hpos
    · rw [h0, pow_zero, one_mul, Nat.one_mul]
      exact pred_mul_add_pred_mod_lt hq hx hxq
    · rw [pow_mul_mod_self_eq_zero hq0 hpos, pow_mul_pred_mod hq hx hpos]
      omega

end Commons.Data.Nat
