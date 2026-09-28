import Mathlib

namespace Work.HP

theorem rpow_le_add_one (x a : ℝ) (hx : 0 < x) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    x ^ a ≤ x + 1 := by
  by_cases h : 1 ≤ x
  · calc x ^ a ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h ha1
      _ = x := Real.rpow_one x
      _ ≤ x + 1 := by linarith
  · push Not at h
    have h1 : x ^ a ≤ 1 := Real.rpow_le_one hx.le h.le ha0.le
    linarith

end Work.HP
