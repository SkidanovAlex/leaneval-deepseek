import Mathlib

namespace Commons.Data.Nat

theorem noCarry_pred_mul {q x : ℕ} (hq : 2 ≤ q) (hx : 1 ≤ x) (hxq : x ≤ q) (i : ℕ) :
    (q - 1) * x / q ^ i % q + (x - 1) / q ^ i % q < q := by
  have hxpos : 0 < x := by omega
  -- (q - 1) * x = q * x - x
  have h1 : (q - 1) * x = q * x - x := by rw [Nat.sub_mul, one_mul]
  -- (x - 1) * q + (q - x) = q * x - x
  have hq_le : q ≤ x * q := Nat.le_mul_of_pos_left q hxpos
  have h2 : (x - 1) * q + (q - x) = q * x - x := by
    calc (x - 1) * q + (q - x)
        = (x * q - q) + (q - x) := by rw [Nat.sub_mul, one_mul]
      _ = (x * q - q + q) - x := (Nat.add_sub_assoc hxq (x * q - q)).symm
      _ = x * q - x := by rw [Nat.sub_add_cancel hq_le]
      _ = q * x - x := by rw [mul_comm]
  have hid : (q - 1) * x = (q - x) + (x - 1) * q := by
    rw [h1, ← h2, add_comm]
  rcases Nat.eq_zero_or_pos i with hi0 | hi
  · rw [hi0]
    simp only [pow_zero, Nat.div_one]
    have hxq1 : x - 1 < q := by omega
    have hb : (x - 1) % q = x - 1 := Nat.mod_eq_of_lt hxq1
    have hqx : q - x < q := by omega
    have ha : (q - 1) * x % q = q - x := by
      rw [hid, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hqx]
    rw [ha, hb]
    omega
  · have hqi : q ≤ q ^ i := Nat.le_self_pow (show i ≠ 0 by omega) q
    have hxqi : x ≤ q ^ i := le_trans hxq hqi
    have hb0 : (x - 1) / q ^ i = 0 := by
      apply Nat.div_eq_of_lt
      omega
    have ha_le : (q - 1) * x / q ^ i ≤ q - 1 := by
      apply Nat.div_le_of_le_mul
      calc (q - 1) * x ≤ (q - 1) * q ^ i := Nat.mul_le_mul_left _ hxqi
        _ = q ^ i * (q - 1) := by ring
    have ha_mod : (q - 1) * x / q ^ i % q = (q - 1) * x / q ^ i := by
      apply Nat.mod_eq_of_lt
      omega
    rw [hb0, ha_mod, Nat.zero_mod, add_zero]
    omega

end Commons.Data.Nat
