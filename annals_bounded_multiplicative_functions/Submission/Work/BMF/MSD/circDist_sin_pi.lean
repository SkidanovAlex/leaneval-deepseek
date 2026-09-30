import Mathlib
import Submission.Work.BMF.MSD.basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.MSD

open Polynomial Finset Real Complex
open Work.BMF
open Work.BMF.MSD

/-- Jordan's inequality for the distance to the nearest integer: `2 * circDist θ ≤ |sin (π θ)|`.
Since `circDist θ = |θ - m| ≤ 1/2` for `m = ⌊θ + 1/2⌋`, and `sin (π θ) = ± sin (π (θ - m))`,
this is `Real.mul_abs_le_abs_sin` (i.e. `(2/π)|x| ≤ |sin x|`) at `x = π * (θ - m)`, using
`Real.sin_add_int_mul_pi`. -/
theorem circDist_sin_pi (θ : ℝ) :
    2 * circDist θ ≤ |Real.sin (θ * Real.pi)| := by
  set m : ℤ := ⌊θ + 1 / 2⌋ with hm
  have hcd : circDist θ = |θ - (m : ℝ)| := by
    rw [circDist, hm]
  have hhalf : |θ - (m : ℝ)| ≤ 1 / 2 := hcd ▸ circDist_le_half θ
  have hpi : 0 < Real.pi := Real.pi_pos
  -- `|π (θ - m)| ≤ π / 2`
  have hx : |(θ - (m : ℝ)) * Real.pi| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    calc |θ - (m : ℝ)| * Real.pi ≤ (1 / 2) * Real.pi :=
          mul_le_mul_of_nonneg_right hhalf hpi.le
      _ = Real.pi / 2 := by ring
  -- Jordan's inequality at `x = π (θ - m)`
  have hkey := Real.mul_abs_le_abs_sin hx
  -- `sin (π θ) = ± sin (π (θ - m))`
  have hsin_eq : Real.sin (θ * Real.pi)
      = (-1 : ℝ) ^ m * Real.sin ((θ - (m : ℝ)) * Real.pi) := by
    rw [show θ * Real.pi = (θ - (m : ℝ)) * Real.pi + (m : ℝ) * Real.pi by ring]
    rw [Real.sin_add_int_mul_pi]
  have hsimpl : |Real.sin (θ * Real.pi)| = |Real.sin ((θ - (m : ℝ)) * Real.pi)| := by
    rw [hsin_eq, abs_mul, abs_zpow]
    simp
  rw [hcd, hsimpl]
  calc 2 * |θ - (m : ℝ)| = 2 / Real.pi * |(θ - (m : ℝ)) * Real.pi| := by
        rw [abs_mul, abs_of_pos hpi]
        field_simp
    _ ≤ |Real.sin ((θ - (m : ℝ)) * Real.pi)| := hkey

end Work.BMF.MSD
