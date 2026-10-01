import Mathlib

namespace Commons.RingTheory.ZMod

theorem prod_signed_quad_expand (N : ℕ) [NeZero N] (P X Y Z T : ZMod N) (hP3 : P ^ 3 = 0) :
    (1 + P * X) * (1 + P * Y) * (1 + P * Z)⁻¹ * (1 + P * T)⁻¹
      = 1 + P * (X + Y - Z - T)
        + P ^ 2 * (X * Y - (X + Y) * (Z + T) + (Z ^ 2 + Z * T + T ^ 2)) := by
  -- Since `P ^ 3 = 0`, we have `(1 + P * W)⁻¹ = 1 - P * W + P ^ 2 * W ^ 2` for every `W`:
  -- multiply `1 + P * W` by that candidate and compute `(1 + a) * (1 - a + a ^ 2) = 1 + a ^ 3`.
  have key : ∀ W : ZMod N, (1 + P * W)⁻¹ = 1 - P * W + P ^ 2 * W ^ 2 := by
    intro W
    have h3 : (P * W) ^ 3 = 0 := by rw [mul_pow, hP3, zero_mul]
    have h : (1 + P * W) * (1 - P * W + P ^ 2 * W ^ 2) = 1 := by
      calc (1 + P * W) * (1 - P * W + P ^ 2 * W ^ 2) = 1 + (P * W) ^ 3 := by ring
        _ = 1 := by rw [h3, add_zero]
    exact ZMod.inv_eq_of_mul_eq_one N _ _ h
  rw [key Z, key T]
  -- The remaining polynomial identity holds by expanding, using `P ^ 3 = 0` to kill high powers.
  linear_combination (T ^ 2 * X + X * Z ^ 2 + T ^ 2 * Y + Y * Z ^ 2 + -1 * T * Z ^ 2
    + -1 * T ^ 2 * Z + P * T ^ 2 * Z ^ 2 + T * X * Z + T * Y * Z + -1 * T * X * Y
    + -1 * X * Y * Z + P * T ^ 2 * X * Y + P * X * Y * Z ^ 2
    + P ^ 2 * T ^ 2 * X * Z ^ 2 + P ^ 2 * T ^ 2 * Y * Z ^ 2 + -1 * P * T * X * Z ^ 2
    + -1 * P * T * Y * Z ^ 2 + -1 * P * T ^ 2 * X * Z + -1 * P * T ^ 2 * Y * Z
    + P * T * X * Y * Z + P ^ 3 * T ^ 2 * X * Y * Z ^ 2 + -1 * P ^ 2 * T * X * Y * Z ^ 2
    + -1 * P ^ 2 * T ^ 2 * X * Y * Z) * hP3

end Commons.RingTheory.ZMod
