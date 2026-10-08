import Mathlib

namespace Work.FUS.DihedralFacts

theorem zmod_two_mul_eq_zero (n : ℕ) [NeZero n] (h2 : Even n) (i : ZMod n)
    (hi : 2 * i = 0) : i = 0 ∨ i = ((n / 2 : ℕ) : ZMod n) := by
  -- Write `n = 2 * (n / 2)` and note `n / 2 > 0`.
  have hn : n = 2 * (n / 2) := by
    have hd : 2 ∣ n := even_iff_two_dvd.mp h2
    have h := Nat.div_mul_cancel hd
    omega
  have hpos : 0 < n / 2 := by
    have hnn : n ≠ 0 := NeZero.ne n
    omega
  -- `i` is the class of its representative `i.val`, so `2 * i.val ≡ 0 [MOD n]`.
  have hcast : ((2 * i.val : ℕ) : ZMod n) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val i]
    exact hi
  have hdiv : n ∣ 2 * i.val := (ZMod.natCast_eq_zero_iff (2 * i.val) n).mp hcast
  have hdiv' : 2 * (n / 2) ∣ 2 * i.val := by rwa [← hn]
  have hm_dvd : n / 2 ∣ i.val :=
    (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 2)).mp hdiv'
  obtain ⟨k, hk⟩ := hm_dvd
  -- Since `i.val < n = 2 * (n / 2)`, the multiplier `k` is `0` or `1`.
  have hlt : i.val < n / 2 * 2 := by
    have h := ZMod.val_lt i
    omega
  have hk2 : k < 2 := by
    have h : n / 2 * k < n / 2 * 2 := by rw [← hk]; exact hlt
    exact (Nat.mul_lt_mul_left hpos).mp h
  rcases (by omega : k = 0 ∨ k = 1) with hk0 | hk1
  · left
    have hv : i.val = 0 := by rw [hk, hk0, mul_zero]
    have h : ((i.val : ℕ) : ZMod n) = 0 := by rw [hv, Nat.cast_zero]
    exact (ZMod.natCast_zmod_val i).symm.trans h
  · right
    have hv : i.val = n / 2 := by rw [hk, hk1, mul_one]
    have h : ((i.val : ℕ) : ZMod n) = ((n / 2 : ℕ) : ZMod n) := by rw [hv]
    exact (ZMod.natCast_zmod_val i).symm.trans h

end Work.FUS.DihedralFacts
