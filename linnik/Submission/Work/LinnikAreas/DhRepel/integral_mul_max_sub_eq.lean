import Mathlib

namespace Work.LinnikAreas.DhRepel

/-- On the interval `[0, L]` with `0 ≤ L`, the factor `max (L - t) 0` agrees with `L - t`,
so the two interval integrals coincide. -/
theorem integral_mul_max_sub_eq (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) :
    ∫ t in (0:ℝ)..L, f t * max (L - t) 0 = ∫ t in (0:ℝ)..L, f t * (L - t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  simp only
  rw [max_eq_left]
  linarith [ht.2, max_eq_right hL]

end Work.LinnikAreas.DhRepel
