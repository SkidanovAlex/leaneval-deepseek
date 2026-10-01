import Mathlib

namespace Work.LinnikAreas

/-- Comparison of a power `x ^ u` with `x + x ^ (5 / 8 - β)` for exponents
`u` in the range `[5 / 8 - β, 1 - β]` (with `5 / 8 ≤ β < 1`) and any `x > 0`.

Both exponents lie in `(-1, 1)`: the lower one is negative, the upper one is
positive but `< 1`.  Accordingly the power `x ^ u` is controlled by the end of
the interval that dominates `x`: for `x ≤ 1` the *smaller* exponent `5 / 8 - β`
gives the larger value, while for `x ≥ 1` the exponent is `≤ 1` and hence
`x ^ u ≤ x`.  Either way `x ^ u` is at most `x + x ^ (5 / 8 - β)`. -/
theorem rpow_le_quarter_range (x β u : ℝ) (hβ : 5 / 8 ≤ β) (hβ1 : β < 1) (hx : 0 < x)
    (ha : 5 / 8 - β ≤ u) (hu : u ≤ 1 - β) :
    x ^ u ≤ x + x ^ (5 / 8 - β) := by
  rcases le_total x 1 with hx1 | hx1
  · -- `x ≤ 1`: the smaller exponent `5 / 8 - β` dominates, and `x ≤ x + x ^ (5 / 8 - β)`.
    have h1 : x ^ u ≤ x ^ (5 / 8 - β) := Real.rpow_le_rpow_of_exponent_ge hx hx1 ha
    have h2 : x ^ (5 / 8 - β) ≤ x + x ^ (5 / 8 - β) := by
      have := Real.rpow_pos_of_pos hx (5 / 8 - β)
      linarith
    linarith
  · -- `x ≥ 1`: since `u ≤ 1 - β ≤ 1` we get `x ^ u ≤ x ^ 1 = x`.
    have hup : u ≤ 1 := by linarith
    have hux : x ^ u ≤ x := by
      have h := Real.rpow_le_rpow_of_exponent_le hx1 hup
      rwa [Real.rpow_one] at h
    have hpos : 0 < x ^ (5 / 8 - β) := Real.rpow_pos_of_pos hx _
    linarith

end Work.LinnikAreas
