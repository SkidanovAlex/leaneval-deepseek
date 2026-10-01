import Mathlib

namespace Work.LinnikAreas

/-- For `x > 0` and exponents `u` between `1 - β` and `1`, the power `x ^ u` is bounded by
`x + x ^ (1 - β)`: below `1` the largest of the two powers is `x ^ (1 - β)`, and above `1`
it is `x = x ^ 1`. -/
theorem rpow_le_upper_range (x β u : ℝ) (hx : 0 < x) (ha : 1 - β ≤ u) (hu : u ≤ 1) :
    x ^ u ≤ x + x ^ (1 - β) := by
  rcases le_total x 1 with hx1 | hx1
  · -- `0 < x ≤ 1`: the exponent is antitone, so `x ^ u ≤ x ^ (1 - β)`.
    have h : x ^ u ≤ x ^ (1 - β) := Real.rpow_le_rpow_of_exponent_ge hx hx1 ha
    nlinarith [Real.rpow_pos_of_pos hx (1 - β)]
  · -- `1 ≤ x`: the exponent is monotone, so `x ^ u ≤ x ^ 1 = x`.
    have h : x ^ u ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hu
    rw [Real.rpow_one] at h
    nlinarith [Real.rpow_pos_of_pos hx (1 - β)]

end Work.LinnikAreas
