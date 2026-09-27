import Mathlib
import Submission.Work.Geo.Radial.Basic

namespace Work.Geo.Radial

open Set Metric
open Work.Geo.Radial

/-- The radial contraction of `ℝᵐ` onto its closed unit ball: a point already inside the ball is
kept, a point outside is scaled by the reciprocal of its (Euclidean) norm.

Writing the scaling factor as `(max 1 ‖x‖)⁻¹` (rather than the piecewise
`if ‖x‖ ≤ 1 then 1 else ‖x‖⁻¹`) makes continuity immediate: the scalar field
`x ↦ (max 1 ‖x‖)⁻¹` is a composition of continuous maps and never vanishes, since
`max 1 ‖x‖ ≥ 1`. -/
noncomputable def radialContraction (m : ℕ) : PL.E m → Metric.closedBall (0 : PL.E m) 1 :=
  fun x => ⟨((max (1 : ℝ) ‖x‖)⁻¹) • x, by
    rw [mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv]
    have hpos : 0 < max (1 : ℝ) ‖x‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
    rw [abs_of_nonneg (le_of_lt hpos)]
    calc (max (1 : ℝ) ‖x‖)⁻¹ * ‖x‖
        ≤ (max (1 : ℝ) ‖x‖)⁻¹ * max (1 : ℝ) ‖x‖ :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr (le_of_lt hpos))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)⟩

theorem continuous_radialContraction (m : ℕ) : Continuous (radialContraction m) :=
  Continuous.subtype_mk
    (((continuous_const.max continuous_norm).inv₀ (fun x => by positivity)).smul continuous_id) _

theorem radialContraction_eq_self (m : ℕ) (x : Metric.closedBall (0 : PL.E m) 1) :
    radialContraction m x = x := by
  apply Subtype.ext
  show ((max (1 : ℝ) ‖(x : PL.E m)‖)⁻¹) • (x : PL.E m) = (x : PL.E m)
  have hx : ‖(x : PL.E m)‖ ≤ 1 := by
    rw [← dist_zero_right]; exact mem_closedBall.mp x.2
  have hmax : max (1 : ℝ) ‖(x : PL.E m)‖ = 1 := max_eq_left hx
  rw [hmax, inv_one, one_smul]

/-- There is a continuous map out of `ℝᵐ` which is the identity on the closed unit ball
(radial contraction onto the ball). -/
theorem exists_continuous_closedBall_selfMap (m : ℕ) :
    ∃ ρ : PL.E m → Metric.closedBall (0 : PL.E m) 1, Continuous ρ ∧
      ∀ x : Metric.closedBall (0 : PL.E m) 1, ρ x = x :=
  ⟨radialContraction m, continuous_radialContraction m, radialContraction_eq_self m⟩

end Work.Geo.Radial
