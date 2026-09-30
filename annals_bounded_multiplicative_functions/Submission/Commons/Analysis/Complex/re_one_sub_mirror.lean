import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped ComplexConjugate

namespace Commons.Analysis.Complex

theorem re_one_sub_mirror {a u : ℂ} {R : ℝ} (hR : 0 < R) (hu : u ≠ a) :
    ((1 / (a - (a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹))).re) =
      -((u - a).re) / (R * R : ℝ) := by
  have hx : u - a ≠ 0 := sub_ne_zero.mpr hu
  have hstarx : (starRingEnd ℂ) (u - a) ≠ 0 := by
    intro h
    apply hx
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'
  have hR2 : (R * R : ℝ) ≠ 0 := ne_of_gt (mul_pos hR hR)
  have hR2c : ((R * R : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR2
  -- a - (a + R^2 * star (u - a)⁻¹) = -R^2 * star (u - a)⁻¹, whose reciprocal
  -- is -star (u - a) / R^2.
  have hmain :
      (1 / (a - (a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹))) =
        -((starRingEnd ℂ) (u - a)) / ((R * R : ℝ) : ℂ) := by
    field_simp [hstarx, hR2c]
    ring
  rw [hmain]
  rw [Complex.div_ofReal_re]
  have hnum : (-(starRingEnd ℂ) (u - a)).re = -((u - a).re) := by
    simp
  rw [hnum]

end Commons.Analysis.Complex
