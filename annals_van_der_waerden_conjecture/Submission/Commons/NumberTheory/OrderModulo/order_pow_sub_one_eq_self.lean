import Mathlib.Data.ZMod.Basic

namespace Commons.NumberTheory.OrderModulo

theorem order_pow_sub_one_eq_self (p f : ℕ) (hp : 2 ≤ p) (hf : 1 ≤ f) :
    orderOf (p : ZMod (p ^ f - 1)) = f := by
  have hp1 : 1 < p := by omega
  have hpk1 : ∀ k, k ≠ 0 → 1 ≤ p ^ k := by
    intro k hk
    exact pow_pos (by omega : 0 < p) k
  have hmod : 0 < p ^ f - 1 := by
    have hf2 : 2 ≤ p ^ f := by
      calc
        2 ≤ p := hp
        _ ≤ p ^ f := le_self_pow (by omega : 1 ≤ p) (by omega : f ≠ 0)
    omega
  apply (orderOf_eq_iff hf).2
  constructor
  · -- x ^ f = 1 where x = (p : ZMod (p^f - 1))
    have htsub : p ^ f - 1 + 1 = p ^ f := by omega
    calc
      (p : ZMod (p ^ f - 1)) ^ f = ((p ^ f : ℕ) : ZMod (p ^ f - 1)) := by
        rw [Nat.cast_pow]
      _ = ((p ^ f - 1 + 1 : ℕ) : ZMod (p ^ f - 1)) := by rw [htsub]
      _ = 1 := by
        rw [Nat.cast_add, Nat.cast_one]
        rw [ZMod.natCast_self, zero_add]
  · -- minimality
    intro k hkf hk0 hkone
    have hx : (p : ZMod (p ^ f - 1)) ^ k = ((p ^ k : ℕ) : ZMod (p ^ f - 1)) := by
      rw [Nat.cast_pow]
    have hcast1 : ((p ^ k : ℕ) : ZMod (p ^ f - 1)) = 1 := by
      rwa [hx] at hkone
    have hpkpos : 1 ≤ p ^ k := hpk1 k (by omega)
    have hpfpos : 1 ≤ p ^ f := hpk1 f (by omega)
    have htsubk : p ^ k - 1 + 1 = p ^ k := by omega
    have hcast2 : (((p ^ k - 1 + 1 : ℕ)) : ZMod (p ^ f - 1)) = 1 := by
      simpa [htsubk] using hcast1
    have hcast3 : (((p ^ k - 1 : ℕ) : ZMod (p ^ f - 1)) + 1) = 1 := by
      simpa [Nat.cast_add, Nat.cast_one] using hcast2
    have hz : ((p ^ k - 1 : ℕ) : ZMod (p ^ f - 1)) = 0 := by
      apply add_right_cancel (b := 1)
      simpa using hcast3
    have hdvd : p ^ f - 1 ∣ p ^ k - 1 := by
      exact (ZMod.natCast_eq_zero_iff (p ^ k - 1) (p ^ f - 1)).mp hz
    have npos : 0 < p ^ k - 1 := by
      have hpk2 : 2 ≤ p ^ k := by
        calc
          2 ≤ p := hp
          _ ≤ p ^ k := le_self_pow (by omega : 1 ≤ p) (by omega : k ≠ 0)
      omega
    have hltn : p ^ k - 1 < p ^ f - 1 := by
      have hpklt : p ^ k < p ^ f := Nat.pow_lt_pow_right hp1 hkf
      omega
    exact (not_le_of_gt hltn) (Nat.le_of_dvd npos hdvd)

end Commons.NumberTheory.OrderModulo