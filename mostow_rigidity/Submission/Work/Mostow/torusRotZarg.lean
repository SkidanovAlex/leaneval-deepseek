import Mathlib
import Submission.Work.Mostow.torusAngleDefs

/-!
# The angle of `rotZ` is the rotation angle

If `u, v` is an orthonormal pair and the linear isometry `c` acts on the oriented plane
`span{u,v}` by sending `u ↦ cos t • u + sin t • v` and `v ↦ -sin t • u + cos t • v`, then
`rotZ u v c = ⟪c u, u⟫ + ⟪c u, v⟫ * I = cos t + sin t * I`, whose argument (as an element of
`Real.Angle`) is `t`.
-/

namespace Work.Mostow

theorem torusRotZarg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    {c : V ≃ₗᵢ[ℝ] V} {t : ℝ}
    (hcu : c u = Real.cos t • u + Real.sin t • v)
    (hcv : c v = -Real.sin t • u + Real.cos t • v) :
    ((Complex.arg (rotZ u v c) : ℝ) : Real.Angle) = (t : Real.Angle) := by
  -- `hcv` is not needed for this computation; record it so the argument is not flagged unused.
  have _hcv := hcv
  have hu2 : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hv2 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have huvu : inner ℝ v u = 0 := by rw [real_inner_comm]; exact huv
  have hzu : inner ℝ (c u) u = Real.cos t := by
    rw [hcu, inner_add_left, real_inner_smul_left, real_inner_smul_left, hu2, huvu]
    ring
  have hzv : inner ℝ (c u) v = Real.sin t := by
    rw [hcu, inner_add_left, real_inner_smul_left, real_inner_smul_left, huv, hv2]
    ring
  have hz : rotZ u v c = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
    rw [rotZ, hzu, hzv]
  rw [hz, ← Real.Angle.cos_coe, ← Real.Angle.sin_coe]
  exact Complex.arg_cos_add_sin_mul_I_coe_angle (t : Real.Angle)

end Work.Mostow
