import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped RealInnerProductSpace
open Real

namespace Work.ConstructionInstance

/-- **The spherical angle is at most twice the chord,** with a generous constant `2` replacing
the sharp `π/2`.  For unit vectors, `‖u - v‖ = 2 sin (angle u v / 2)`, and Jordan's inequality
`Real.mul_le_sin` (`(2/π) t ≤ sin t`) converts this into `angle u v ≤ (π/2) ‖u - v‖ ≤ 2 ‖u - v‖`;
equivalently one may show `cos (2 ‖u - v‖) ≤ ⟪u,v⟫` (using `Real.one_sub_sq_div_two_le_cos` and
`‖u - v‖ ^ 2 = 2 - 2 * ⟪u,v⟫`) in the case `2 ‖u - v‖ ≤ π`, and `angle u v ≤ π ≤ 2 ‖u - v‖`
otherwise. -/
theorem angle_le_two_mul_norm_sub {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    InnerProductGeometry.angle u v ≤ 2 * ‖u - v‖ := by
  -- `cos (angle u v) = ⟪u,v⟫` for unit vectors.
  have hinner : ⟪u, v⟫ = Real.cos (InnerProductGeometry.angle u v) := by
    rw [InnerProductGeometry.cos_angle, hu, hv, mul_one, div_one]
  -- `‖u - v‖² = 2 - 2⟪u,v⟫`.
  have hsub : ‖u - v‖ ^ 2 = 2 - 2 * ⟪u, v⟫ := by
    rw [norm_sub_pow_two_real, hu, hv]; ring
  -- hence `cos (angle u v) = 1 - ‖u - v‖² / 2`.
  have hcos : Real.cos (InnerProductGeometry.angle u v) = 1 - ‖u - v‖ ^ 2 / 2 := by
    rw [← hinner, hsub]; ring
  rcases le_or_gt (2 * ‖u - v‖) π with h | h
  · -- The interesting case: `2 ‖u - v‖ ≤ π`.  Set `t = 2 ‖u - v‖` and show `cos t ≤ cos (angle)`.
    set t := 2 * ‖u - v‖ with ht
    have ht0 : 0 ≤ t := by rw [ht]; positivity
    have htt : t ≤ π := by rw [ht]; linarith
    have habs : |t| ≤ π := abs_le.mpr ⟨by linarith, htt⟩
    -- quadratic upper bound for `cos` on `[-π, π]`
    have hcost : Real.cos t ≤ 1 - 2 / π ^ 2 * t ^ 2 := Real.cos_le_one_sub_mul_cos_sq habs
    have hcosa : Real.cos (InnerProductGeometry.angle u v) = 1 - t ^ 2 / 8 := by
      rw [hcos, ht]; ring
    -- `1/8 ≤ 2/π²`, i.e. `π² ≤ 16`, i.e. `π ≤ 4`.
    have hcoef : (1:ℝ)/8 ≤ 2 / π ^ 2 := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [Real.pi_pos, Real.pi_lt_four]
    have hkey : 1 - 2 / π ^ 2 * t ^ 2 ≤ 1 - t ^ 2 / 8 := by
      have hm : (1:ℝ)/8 * t ^ 2 ≤ 2 / π ^ 2 * t ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg t)
      linarith
    have hcle : Real.cos t ≤ Real.cos (InnerProductGeometry.angle u v) := by
      rw [hcosa]; linarith
    -- `cos` is strictly decreasing on `[0, π]`, so `cos t ≤ cos (angle)` forces `angle ≤ t`.
    have hfin : InnerProductGeometry.angle u v ≤ t := by
      by_contra hc
      rw [not_le] at hc
      have := Real.cos_lt_cos_of_nonneg_of_le_pi ht0 (InnerProductGeometry.angle_le_pi u v) hc
      linarith
    exact hfin
  · -- Otherwise `π < 2 ‖u - v‖`, and `angle u v ≤ π` finishes it.
    linarith [InnerProductGeometry.angle_le_pi u v]

end Work.ConstructionInstance
