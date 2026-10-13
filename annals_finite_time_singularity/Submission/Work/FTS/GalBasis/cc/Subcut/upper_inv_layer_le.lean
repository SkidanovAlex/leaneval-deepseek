import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.GalBasis.cc.wwLayers

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

/-- The mirror of `layer_int_pow_le` at `γ = 1`: the angular layer `[π/2 - 2t, π/2 - t]` near `π/2` carries at most `π/4` of `sin(2θ)⁻¹`. -/
theorem upper_inv_layer_le (t : ℝ) (ht : 0 < t) (ht2 : 2 * t ≤ Real.pi / 4) :
    ∫ θ in (Real.pi / 2 - 2 * t)..(Real.pi / 2 - t), (Real.sin (2 * θ))⁻¹ ≤ Real.pi / 4 := by
  -- The layer is the reflection of `[t, 2t]` about `π/4`; the substitution `θ ↦ π/2 - θ`
  -- carries `sin (2θ)` to `sin (2θ)` (since `sin (π - x) = sin x`) and the interval
  -- `[π/2 - 2t, π/2 - t]` to `[t, 2t]`.  So the statement is exactly `layer_int_pow_le`
  -- at `γ = 1`.
  have hbase := Work.FTS.GalBasis.cc.layer_int_pow_le (γ := 1) (t := t) (by norm_num) ht ht2
  have hbase' : ∫ θ in t..(2 * t), (Real.sin (2 * θ))⁻¹ ≤ Real.pi / 4 := by
    have h1 : (fun θ : ℝ => Real.sin (2 * θ) ^ (-1 : ℝ) * θ ^ ((1 : ℝ) - 1))
        = fun θ => (Real.sin (2 * θ))⁻¹ := by
      funext θ
      rw [Real.rpow_neg_one, show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, mul_one]
    rw [h1, Real.rpow_one] at hbase
    exact hbase
  have hsub := intervalIntegral.integral_comp_add_mul (c := (-1 : ℝ))
    (a := Real.pi / 2 - 2 * t) (b := Real.pi / 2 - t) (fun x : ℝ => (Real.sin (2 * x))⁻¹)
    (by norm_num) (Real.pi / 2)
  have hL : ∫ x in (Real.pi / 2 - 2 * t)..(Real.pi / 2 - t), (Real.sin (2 * x))⁻¹
      = ∫ x in (Real.pi / 2 - 2 * t)..(Real.pi / 2 - t),
          (Real.sin (2 * (Real.pi / 2 + -1 * x)))⁻¹ := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    rw [show 2 * (Real.pi / 2 + -1 * x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]
  rw [hL, hsub]
  rw [show Real.pi / 2 + -1 * (Real.pi / 2 - 2 * t) = 2 * t by ring,
    show Real.pi / 2 + -1 * (Real.pi / 2 - t) = t by ring,
    show ((-1 : ℝ)⁻¹) = -1 by norm_num, neg_one_smul]
  rw [← intervalIntegral.integral_symm (2 * t) t]
  exact hbase'

end Work.FTS.GalBasis.cc.Subcut
