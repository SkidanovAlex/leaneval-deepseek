import Mathlib

namespace Work.HP.EE

/-- For `1 ≤ d` and `0 ≤ x ≤ y` one has `y^d - x^d ≥ (y - x) * y^(d-1)`. -/
lemma pow_sub_pow_ge (d : ℕ) (hd : 1 ≤ d) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (y - x) * y ^ (d - 1) ≤ y ^ d - x ^ d := by
  -- `x^(d-1) ≤ y^(d-1)` since `0 ≤ x ≤ y`.
  have hxpow : x ^ (d - 1) ≤ y ^ (d - 1) := pow_le_pow_left₀ hx hxy (d - 1)
  -- hence `x^d = x * x^(d-1) ≤ x * y^(d-1)`
  have hxd_eq : x ^ d = x * x ^ (d - 1) := by
    conv_lhs => rw [show d = (d - 1) + 1 from by omega]
    rw [pow_succ']
  have hxd : x ^ d ≤ x * y ^ (d - 1) := by
    rw [hxd_eq]
    exact mul_le_mul_of_nonneg_left hxpow hx
  -- and `(y - x) * y^(d-1) = y^d - x * y^(d-1)`
  have hyd : (y - x) * y ^ (d - 1) = y ^ d - x * y ^ (d - 1) := by
    have hyd' : y ^ d = y * y ^ (d - 1) := by
      conv_lhs => rw [show d = (d - 1) + 1 from by omega]
      rw [pow_succ']
    rw [hyd']
    ring
  rw [hyd]
  exact sub_le_sub_left hxd (y ^ d)

end Work.HP.EE
