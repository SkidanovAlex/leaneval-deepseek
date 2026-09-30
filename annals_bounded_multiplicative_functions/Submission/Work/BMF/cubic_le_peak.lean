import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The maximum of `x ↦ A x - B x ^ 3` on `x ≥ 0` is attained at
`s = sqrt (A / (3 * B))` and equals `(2 / 3) * A * s`. -/
theorem cubic_le_peak (A B x : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (hx : 0 ≤ x) :
    A * x - B * x ^ 3 ≤ (2 / 3) * A * Real.sqrt (A / (3 * B)) := by
  have hB3 : (0:ℝ) < 3 * B := by linarith
  have hA3B : 0 ≤ A / (3*B) := div_nonneg hA hB3.le
  set s := Real.sqrt (A/(3*B)) with hs
  have hs2 : s^2 = A/(3*B) := Real.sq_sqrt hA3B
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hAeq : A = 3*B*s^2 := by rw [hs2]; field_simp
  rw [hAeq]
  -- now reduce to `(x - s)^2 * (x + 2*s) ≥ 0`
  have hkey : 0 ≤ B * ((x - s)^2 * (x + 2*s)) := by
    apply mul_nonneg hB.le
    apply mul_nonneg (sq_nonneg _)
    linarith
  nlinarith [hkey]

end Work.BMF
