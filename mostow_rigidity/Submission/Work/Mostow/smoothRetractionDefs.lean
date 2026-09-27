import Mathlib

/-! # Auxiliary definitions for smoothing a continuous retraction

We define the radial projection onto the closed unit ball of a real normed space, which is used
to extend a map defined on the closed unit ball to the whole space. -/

namespace Work.Mostow

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial projection of a normed space onto its closed unit ball: `x ↦ x / max 1 ‖x‖`. -/
noncomputable def ballProj (x : E) : E := (max 1 ‖x‖)⁻¹ • x

theorem ballProj_of_le {x : E} (hx : ‖x‖ ≤ 1) : ballProj x = x := by
  simp [ballProj, max_eq_left hx]

theorem ballProj_of_one_le {x : E} (hx : 1 ≤ ‖x‖) : ballProj x = ‖x‖⁻¹ • x := by
  simp [ballProj, max_eq_right hx]

theorem ballProj_continuous : Continuous (ballProj : E → E) := by
  unfold ballProj
  refine (Continuous.inv₀ (continuous_const.max continuous_norm) ?_).smul continuous_id
  intro x
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

theorem ballProj_norm_le_one (x : E) : ‖ballProj x‖ ≤ 1 := by
  have hpos : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h : (max 1 ‖x‖)⁻¹ * ‖x‖ ≤ (max 1 ‖x‖)⁻¹ * max 1 ‖x‖ :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr hpos.le)
  rw [inv_mul_cancel₀ hpos.ne'] at h
  rw [ballProj, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
  exact h

theorem ballProj_mem_closedBall (x : E) : ballProj x ∈ closedBall 0 1 := by
  rw [mem_closedBall_zero_iff]
  exact ballProj_norm_le_one x

theorem ballProj_eq_self {x : E} (hx : x ∈ closedBall 0 1) : ballProj x = x :=
  ballProj_of_le (by rwa [mem_closedBall_zero_iff] at hx)

theorem ballProj_isFixedPt (x : E) : ballProj (ballProj x) = ballProj x :=
  ballProj_eq_self (ballProj_mem_closedBall x)

end Work.Mostow
