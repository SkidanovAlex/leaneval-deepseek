/-
Copyright: work module for the Elgindi finite-time singularity project.

# The one-dimensional two-scale optimisation

If `F²` is dominated, at *every* scale `t ∈ (0, π/2)`, by the two-term expression
`(2/3) t³ Y + 72 t⁻¹ X`, then `F² ≤ 100 (X + √(XY))`.  The two branches of the argument are
`Y ≤ X` (evaluate at the fixed scale `t = π/4`, where the two coefficients are bounded: the
`t³`-coefficient by `1` and `72 t⁻¹ = 288/π < 96`) and `X < Y` (evaluate at the optimal scale
`t = (X/Y)^{1/4} ≤ 1`, where `t³ Y = X/t = X^{3/4}Y^{1/4} ≤ √(XY)`); the degenerate case `X = 0`
is handled by letting `t → 0⁺`.
-/
import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.EndpointValues

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The two-scale optimisation.** -/
theorem endpointSqBound {X Y F : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      F ^ 2 ≤ (2 / 3) * t ^ 3 * Y + 72 * t⁻¹ * X) :
    F ^ 2 ≤ 100 * (X + Real.sqrt (X * Y)) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  rcases eq_or_lt_of_le hX with hX0 | hXpos
  · -- degenerate case `X = 0`: let `t → 0⁺`
    have hlim : Filter.Tendsto (fun t : ℝ => (2 / 3) * t ^ 3 * Y)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h3 : Filter.Tendsto (fun t : ℝ => t ^ 3) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds 0) := by
        have hcont : Continuous (fun t : ℝ => t ^ 3) := by fun_prop
        simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      have h4 := (h3.const_mul ((2 : ℝ) / 3)).const_mul Y
      simpa [mul_assoc, mul_left_comm, mul_comm] using h4
    have hle : F ^ 2 ≤ 0 := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin,
        Filter.le_def.mp nhdsWithin_le_nhds _ (Iio_mem_nhds hpi)] with t ht0 ht1
      have h' := h t ht0 ht1
      rw [← hX0] at h'
      simpa using h'
    rw [← hX0]
    simpa using hle
  · by_cases hYX : Y ≤ X
    · -- `Y ≤ X`: evaluate at `t = π/4`
      have h4pos : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
      have h4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
      have h' := h (Real.pi / 4) h4pos h4lt
      have hcoef : (2 / 3) * (Real.pi / 4) ^ 3 + 72 * (Real.pi / 4)⁻¹ ≤ 100 := by
        have h1 : (2 / 3) * (Real.pi / 4) ^ 3 ≤ 2 / 3 := by
          have hlt : Real.pi / 4 < 1 := by linarith [Real.pi_lt_four]
          have h0 : (0 : ℝ) ≤ Real.pi / 4 := le_of_lt h4pos
          have h3 : (Real.pi / 4) ^ 3 ≤ 1 := by
            exact pow_le_one₀ h0 hlt.le
          nlinarith
        have h2 : 72 * (Real.pi / 4)⁻¹ ≤ 96 := by
          have h3 : (3 : ℝ) / 4 < Real.pi / 4 := by linarith [Real.pi_gt_three]
          have h4 : (Real.pi / 4)⁻¹ < 4 / 3 := by
            rw [inv_eq_one_div]
            have := one_div_lt_one_div_of_lt (show (0 : ℝ) < 3 / 4 by norm_num) h3
            simpa using this
          linarith
        linarith
      calc F ^ 2 ≤ (2 / 3) * (Real.pi / 4) ^ 3 * Y + 72 * (Real.pi / 4)⁻¹ * X := h'
        _ ≤ (2 / 3) * (Real.pi / 4) ^ 3 * X + 72 * (Real.pi / 4)⁻¹ * X := by
            have hmono : (2 / 3) * (Real.pi / 4) ^ 3 * Y ≤ (2 / 3) * (Real.pi / 4) ^ 3 * X :=
              mul_le_mul_of_nonneg_left hYX (by positivity)
            linarith
        _ = ((2 / 3) * (Real.pi / 4) ^ 3 + 72 * (Real.pi / 4)⁻¹) * X := by ring
        _ ≤ 100 * X := mul_le_mul_of_nonneg_right hcoef hX
        _ ≤ 100 * (X + Real.sqrt (X * Y)) := by
            have hnn : (0 : ℝ) ≤ Real.sqrt (X * Y) := Real.sqrt_nonneg _
            linarith
    · -- `0 < X < Y`: evaluate at the optimal scale `t = (X/Y)^{1/4}`
      have hXY : X < Y := not_le.mp hYX
      have hYpos : 0 < Y := lt_trans hXpos hXY
      set u := Real.sqrt X with hu
      set v := Real.sqrt Y with hv
      have hu2 : u ^ 2 = X := Real.sq_sqrt hX
      have hv2 : v ^ 2 = Y := Real.sq_sqrt hY
      have hu0 : 0 < u := Real.sqrt_pos.2 hXpos
      have hv0 : 0 < v := Real.sqrt_pos.2 hYpos
      set t := Real.sqrt (u / v) with ht
      have htpos : 0 < t := Real.sqrt_pos.2 (div_pos hu0 hv0)
      have ht2 : t ^ 2 = u / v := Real.sq_sqrt (le_of_lt (div_pos hu0 hv0))
      have htle1 : t ≤ 1 := by
        rw [← Real.sqrt_one]
        refine Real.sqrt_le_sqrt ?_
        rw [div_le_one hv0]
        rw [hu, hv]
        exact Real.sqrt_le_sqrt hXY.le
      have htlt : t < Real.pi / 2 := by linarith [Real.pi_gt_three, htle1]
      have h' := h t htpos htlt
      have htne : t ≠ 0 := ne_of_gt htpos
      have ht4 : t ^ 4 = X / Y := by
        rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2, div_pow, hu2, hv2]
      have hkey : t ^ 3 * Y = X / t := by
        have h1 : (t ^ 3 * Y) * t = X := by
          calc (t ^ 3 * Y) * t = t ^ 4 * Y := by ring
            _ = (X / Y) * Y := by rw [ht4]
            _ = X := by field_simp
        field_simp
        linarith [h1]
      have ht2Y : t ^ 2 * Y = Real.sqrt (X * Y) := by
        have hYv : Y / v = v := by
          rw [← hv2]
          field_simp
        calc t ^ 2 * Y = (u / v) * Y := by rw [ht2]
          _ = u * (Y / v) := by ring
          _ = u * v := by rw [hYv]
          _ = Real.sqrt X * Real.sqrt Y := by rw [hu, hv]
          _ = Real.sqrt (X * Y) := by rw [Real.sqrt_mul hX]
      have hXt : X / t ≤ Real.sqrt (X * Y) := by
        rw [← ht2Y, ← hkey]
        have ht3 : t ^ 3 ≤ t ^ 2 := by
          nlinarith [htpos, htle1, sq_nonneg t, sq_nonneg (1 - t)]
        exact mul_le_mul_of_nonneg_right ht3 hY
      have hfinal : (2 / 3) * t ^ 3 * Y + 72 * t⁻¹ * X ≤ 100 * (X + Real.sqrt (X * Y)) := by
        have e1 : (2 / 3) * t ^ 3 * Y = (2 / 3) * (X / t) := by rw [mul_assoc, hkey]
        have e2 : 72 * t⁻¹ * X = 72 * (X / t) := by ring
        rw [e1, e2]
        have hmid : (2 / 3) * (X / t) + 72 * (X / t) ≤ 100 * Real.sqrt (X * Y) := by
          have h100 : (2 / 3 : ℝ) + 72 ≤ 100 := by norm_num
          have hcomb : (2 / 3) * (X / t) + 72 * (X / t) = ((2 / 3) + 72) * (X / t) := by ring
          rw [hcomb]
          calc ((2 / 3) + 72) * (X / t) ≤ 100 * (X / t) :=
                mul_le_mul_of_nonneg_right h100 (by positivity)
            _ ≤ 100 * Real.sqrt (X * Y) := mul_le_mul_of_nonneg_left hXt (by norm_num)
        have hnn : (0 : ℝ) ≤ Real.sqrt (X * Y) := Real.sqrt_nonneg _
        linarith [hmid, hX, hnn]
      linarith [h', hfinal]

end Work.EllipticEst.Core.i0Aux.EndpointValues
