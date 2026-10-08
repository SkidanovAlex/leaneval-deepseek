import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

/-- Arithmetic core of the two-torsion computation.

If `x < 2^m` is such that `2^m ∣ 2 * x`, then `x` is either `0` or the unique
element `2^(m-1)` of additive order two in `ℤ/2^m`. -/
theorem nat_two_pow_dvd_two_mul {m x : ℕ} (hx : x < 2 ^ m) (h : 2 ^ m ∣ 2 * x) :
    x = 0 ∨ x = 2 ^ (m - 1) := by
  obtain ⟨k, hk⟩ := h
  have hk2 : k < 2 := by
    have hlt : 2 * x < 2 * 2 ^ m := by nlinarith [hx]
    have h2 : (2 : ℕ) ^ m * 2 = 2 * 2 ^ m := by ring
    have h1 : 2 ^ m * k < 2 ^ m * 2 := by rw [← hk, h2]; exact hlt
    exact Nat.lt_of_mul_lt_mul_left h1
  interval_cases k
  · left; omega
  · right
    have hk' : 2 * x = 2 ^ m := by simpa using hk
    have hm : 0 < m := by
      rcases m with _ | m
      · omega
      · omega
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hm]
      rw [pow_succ', Nat.pred_eq_sub_one]
    have hx2 : 2 * x = 2 * 2 ^ (m - 1) := by rw [hk', hpow]
    exact Nat.mul_left_cancel (by norm_num) hx2

/-- The 2-torsion of `ZMod (2^m)`: an element `x` with `2 * x = 0` is either `0`
or the unique element of additive order two, `2^(m-1)`. -/
theorem zmod_two_torsion {m : ℕ} {x : ZMod (2 ^ m)} (h : 2 * x = 0) : x = 0 ∨ x = 2 ^ (m - 1) := by
  have hdiv : 2 ^ m ∣ 2 * x.val := by
    have h1 : ((2 * x.val : ℕ) : ZMod (2 ^ m)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val, h]
    exact (ZMod.natCast_eq_zero_iff (2 * x.val) (2 ^ m)).mp h1
  rcases nat_two_pow_dvd_two_mul (ZMod.val_lt x) hdiv with hv | hv
  · left
    exact (ZMod.val_eq_zero x).mp hv
  · right
    rw [show x = ((x.val : ℕ) : ZMod (2 ^ m)) from (ZMod.natCast_zmod_val x).symm, hv]
    push_cast
    rfl

end Work.Hering.HardCore
