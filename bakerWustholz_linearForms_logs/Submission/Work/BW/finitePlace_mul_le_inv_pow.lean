import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- At a finite place `w` of a number field, if `x` and `c ^ n * y * z` both have value `≤ 1`
(i.e. both are `w`-integers) then `w (x * y * z) ≤ 1 / (w c) ^ n` (the hypothesis `0 < w c`
is exactly what `FinitePlace.pos_iff` supplies for `c ≠ 0`). -/
theorem finitePlace_mul_le_inv_pow {L : Type*} [Field L] [NumberField L]
    (w : NumberField.FinitePlace L) {c x y z : L} {n : ℕ}
    (hc0 : 0 < w c) (hx : w x ≤ 1) (hyz : w (c ^ n * y * z) ≤ 1) :
    w (x * y * z) ≤ 1 / (w c) ^ n := by
  have hcn : 0 < (w c) ^ n := pow_pos hc0 n
  -- `w` is multiplicative and additive-nonnegative, so it is multiplicative on products.
  have h1 : w (c ^ n * y * z) = w c ^ n * (w y * w z) := by
    rw [map_mul, map_mul, map_pow, mul_assoc]
  rw [h1] at hyz
  have h2 : w y * w z ≤ 1 / (w c) ^ n := by
    rw [le_div_iff₀ hcn]
    linarith [hyz]
  calc w (x * y * z) = w x * (w y * w z) := by rw [map_mul, map_mul, mul_assoc]
    _ ≤ 1 * (w y * w z) := by
        apply mul_le_mul_of_nonneg_right hx
        positivity
    _ = w y * w z := one_mul _
    _ ≤ 1 / (w c) ^ n := h2

end Work.BW
