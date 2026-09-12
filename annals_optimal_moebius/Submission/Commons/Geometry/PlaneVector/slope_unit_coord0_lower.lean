import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Geometry.PlaneVector

open Filter

set_option autoImplicit false

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- For a UNIT vector `v : ℝ²` whose slope `v₁/v₀` is bounded in absolute
value by `C ≥ 0`, the first coordinate is bounded away from 0:
`1 / √(1 + C²) ≤ |v 0|`.  (Equivalently: a unit vector nearly parallel to
the vertical axis is exactly one with unbounded slope; here the slope is
bounded, so the vector is uniformly far from vertical.) -/
theorem slope_unit_coord0_lower {v : EuclideanSpace ℝ (Fin 2)} {C : ℝ}
    (hC : 0 ≤ C) (hv0 : v 0 ≠ 0) (hunit : ‖v‖ = 1)
    (hslope : |v 1 / v 0| ≤ C) :
    1 / Real.sqrt (1 + C ^ 2) ≤ |v 0| := by
  -- v has unit Euclidean norm, so (v 0)² + (v 1)² = 1.
  have hsum : (v 0)^2 + (v 1)^2 = 1 := by
    have hnorm : ‖v‖ ^ 2 = ∑ i : Fin 2, ‖v i‖ ^ 2 :=
      PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 2 => ℝ) v
    rw [hunit] at hnorm
    norm_num at hnorm
    simpa [Fin.sum_univ_two] using hnorm.symm
  -- |v 1 / v 0| ≤ C with C ≥ 0, rewritten in terms of absolute values.
  have hdiv : |v 1| / |v 0| ≤ C := by
    simpa [abs_div] using hslope
  have hposAbs : 0 < |v 0| := abs_pos.mpr hv0
  have habs : |v 1| ≤ C * |v 0| := by
    rwa [div_le_iff₀ hposAbs] at hdiv
  -- Squaring gives (v 1)² ≤ C² * (v 0)².
  have hsq : (v 1)^2 ≤ C^2 * (v 0)^2 := by
    have h3 : |v 1|^2 ≤ (C * |v 0|)^2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (abs_nonneg (v 1)), abs_of_nonneg (mul_nonneg hC (abs_nonneg (v 0)))]
      exact habs
    calc
      (v 1)^2 = |v 1|^2 := by rw [sq_abs]
      _ ≤ (C * |v 0|)^2 := h3
      _ = C^2 * |v 0|^2 := by rw [mul_pow]
      _ = C^2 * (v 0)^2 := by rw [sq_abs]
  -- 1 = (v 0)² + (v 1)² ≤ (v 0)² (1 + C²), hence (v 0)² ≥ 1 / (1 + C²).
  have hdenpos : 0 < 1 + C ^ 2 := by nlinarith [sq_nonneg C]
  have h5 : 1 ≤ (1 + C^2) * (v 0)^2 := by
    nlinarith [hsum, hsq]
  have h6 : 1 / (1 + C^2) ≤ (v 0)^2 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [h5]
  -- Conclude 1 / √(1 + C²) ≤ |v 0| by squaring back.
  exact le_of_sq_le_sq (by
    calc
      (1 / Real.sqrt (1 + C ^ 2)) ^ 2 = 1 / (Real.sqrt (1 + C ^ 2) ^ 2) := by
        rw [div_pow]
        norm_num
      _ = 1 / (1 + C ^ 2) := by rw [Real.sq_sqrt (le_of_lt hdenpos)]
      _ ≤ (v 0) ^ 2 := h6
      _ = |v 0| ^ 2 := by rw [sq_abs]) (abs_nonneg (v 0))

end Commons.Geometry.PlaneVector