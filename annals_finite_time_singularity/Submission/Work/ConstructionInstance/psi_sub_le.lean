/-
# `Work.ConstructionInstance.psi_sub_le`

`psi x = arccos (r x / ρ x)` (the corrected polar angle, `r = Cyl.radial`, `ρ = Cyl.rho = ‖·‖`) is
Lipschitz with constant `1 / ρ` on the region `ρ ≥ ρ₀ > 0`:

  `|psi x - psi y| ≤ 4 π ‖x - y‖ / ρ₀`     (`‖x - y‖ = dist x y`).

Geometrically `psi x` is the (acute) angle between `x` and the plane `x₃ = 0`, i.e. the distance on
the unit sphere from the direction `x/ρ x` to the equator, and the estimate is the `1`-Lipschitz
property of a distance-to-a-set function, with the chord-to-arc conversion
`angle u v ≤ 2 ‖u - v‖` and the `2 / ρ₀` bound for the normalized vectors.  The constant `4 π` is
generously large; the proof below actually gives `4` in place of `4 π`.

The two non-trivial geometric inputs live in their own files

* `Submission.Work.ConstructionInstance.abs_psi_sub_le_angle` : `|psi x - psi y| ≤ angle x y`,
* `Submission.Work.ConstructionInstance.angle_le_two_mul_norm_sub` :
  `angle u v ≤ 2 ‖u - v‖` for unit `u`, `v`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Submission.Work.ConstructionInstance.GCompDefs
import Submission.Work.ConstructionInstance.abs_psi_sub_le_angle
import Submission.Work.ConstructionInstance.angle_le_two_mul_norm_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set

namespace Work.ConstructionInstance

/-- The normalized vectors of two points of norm `≥ ρ₀ > 0` are at distance at most
`2 ‖x - y‖ / ρ₀` (a generous form of `‖x/‖x‖ - y/‖y‖‖ ≤ 2 ‖x-y‖ / min ‖x‖ ‖y‖`). -/
theorem norm_normalize_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x y : V} {ρ₀ : ℝ} (h₀ : 0 < ρ₀) (hx : ρ₀ ≤ ‖x‖) (hy : ρ₀ ≤ ‖y‖) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * dist x y / ρ₀ := by
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le h₀ hx
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le h₀ hy
  have hsplit : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y
      = ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by
    rw [smul_sub, sub_smul]; abel
  have h2 : |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
    rw [inv_sub_inv hx0.ne' hy0.ne', abs_div, abs_mul, abs_of_pos hx0, abs_of_pos hy0]
    field_simp
  have h1 : ‖‖x‖⁻¹ • (x - y)‖ = ‖x‖⁻¹ * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hx0.le)]
  have hterm : ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, h2]
  calc ‖NormedSpace.normalize x - NormedSpace.normalize y‖
      = ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ := by rw [NormedSpace.normalize, NormedSpace.normalize]
    _ = ‖‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := by rw [hsplit]
    _ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := norm_add_le _ _
    _ = ‖x‖⁻¹ * ‖x - y‖ + |‖y‖ - ‖x‖| / ‖x‖ := by rw [h1, hterm]
    _ = ‖x - y‖ / ‖x‖ + |‖y‖ - ‖x‖| / ‖x‖ := by rw [inv_mul_eq_div]
    _ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ := by
        gcongr
        rw [abs_sub_comm]
        exact abs_norm_sub_norm_le x y
    _ = 2 * ‖x - y‖ / ‖x‖ := by ring
    _ ≤ 2 * ‖x - y‖ / ρ₀ := div_le_div_of_nonneg_left (by positivity) h₀ hx
    _ = 2 * dist x y / ρ₀ := by rw [dist_eq_norm]

/-- **`psi` is `1/ρ`-Lipschitz on `ρ ≥ ρ₀`.**  Chain:
`|psi x - psi y| ≤ angle x y = angle (x/‖x‖) (y/‖y‖) ≤ 2 ‖x/‖x‖ - y/‖y‖‖ ≤ 4 dist x y / ρ₀`,
and `4 ≤ 4 π`. -/
theorem psi_sub_le (x y : R3) {ρ₀ : ℝ} (h₀ : 0 < ρ₀)
    (hx : ρ₀ ≤ Work.Cyl.rho x) (hy : ρ₀ ≤ Work.Cyl.rho y) :
    |psi x - psi y| ≤ 4 * Real.pi * dist x y / ρ₀ := by
  have hρx : 0 < Work.Cyl.rho x := lt_of_lt_of_le h₀ hx
  have hρy : 0 < Work.Cyl.rho y := lt_of_lt_of_le h₀ hy
  have hxn : x ≠ 0 := by
    intro h; rw [h, Work.Cyl.rho_eq_norm, norm_zero] at hρx; exact lt_irrefl 0 hρx
  have hyn : y ≠ 0 := by
    intro h; rw [h, Work.Cyl.rho_eq_norm, norm_zero] at hρy; exact lt_irrefl 0 hρy
  have hA : |psi x - psi y| ≤
      InnerProductGeometry.angle (NormedSpace.normalize x) (NormedSpace.normalize y) := by
    refine (abs_psi_sub_le_angle x y hρx hρy).trans_eq ?_
    rw [InnerProductGeometry.angle_normalize_left, InnerProductGeometry.angle_normalize_right]
  have hB : InnerProductGeometry.angle (NormedSpace.normalize x) (NormedSpace.normalize y)
      ≤ 2 * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ :=
    angle_le_two_mul_norm_sub (NormedSpace.norm_normalize hxn) (NormedSpace.norm_normalize hyn)
  have hC : ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * dist x y / ρ₀ :=
    norm_normalize_sub_le h₀ (by rw [← Work.Cyl.rho_eq_norm]; exact hx)
      (by rw [← Work.Cyl.rho_eq_norm]; exact hy)
  calc |psi x - psi y|
      ≤ 2 * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ := hA.trans hB
    _ ≤ 2 * (2 * dist x y / ρ₀) := mul_le_mul_of_nonneg_left hC (by norm_num)
    _ = 4 * dist x y / ρ₀ := by ring
    _ ≤ 4 * Real.pi * dist x y / ρ₀ := by
        have h1 : 4 * dist x y / ρ₀ = 4 * (dist x y / ρ₀) := by ring
        have h2 : 4 * Real.pi * dist x y / ρ₀ = (4 * Real.pi) * (dist x y / ρ₀) := by ring
        rw [h1, h2]
        exact mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three])
          (div_nonneg dist_nonneg h₀.le)

end Work.ConstructionInstance
