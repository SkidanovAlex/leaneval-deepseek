import Mathlib

/-!
# Minimum modulus principle for the divided slope `dslope f 0`

If `f` is holomorphic on the unit disc, `f 0 = 0`, `f'(0) ≠ 0`, `f` has no zero on the closed
unit disc except at `0`, and `‖f z‖ ≥ c > 0` on the unit circle, then `‖f z‖ ≥ c ‖z‖` on the
whole closed unit disc.

The proof reduces to the maximum modulus principle for the reciprocal of the divided slope
`g = dslope f 0`, which is holomorphic on the disc (Riemann's removable singularity /
`Complex.differentiableOn_dslope`), has no zero on the closed disc, and satisfies `‖g z‖ ≥ c`
on the circle.
-/

namespace Work.CLift

open Metric

theorem min_modulus_dslope {f : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (hd : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hgc : ContinuousOn (dslope f (0 : ℂ)) (Metric.closedBall (0 : ℂ) 1))
    (h0 : f 0 = 0)
    (hderiv : deriv f 0 ≠ 0)
    (hne : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ 1 → f z ≠ 0)
    (hbd : ∀ z : ℂ, ‖z‖ = 1 → c ≤ ‖f z‖) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → c * ‖z‖ ≤ ‖f z‖ := by
  have h1pos : (0 : ℝ) < 1 := by norm_num
  have hball_ne : (1 : ℝ) ≠ 0 := by norm_num
  set g : ℂ → ℂ := dslope f 0 with hgdef
  -- `g` is holomorphic on the disc
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 1) := by
    rw [hgdef]
    exact (Complex.differentiableOn_dslope (Metric.ball_mem_nhds 0 h1pos)).mpr hd
  -- `g` does not vanish on the closed disc
  have hgne : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, g w ≠ 0 := by
    intro w hw
    rw [hgdef]
    have hw' : ‖w‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hw
      exact hw
    rcases eq_or_ne w 0 with hw0 | hw0
    · subst hw0; rw [dslope_same]; exact hderiv
    · rw [dslope_of_ne f hw0, slope_def_module]
      rw [smul_eq_mul]
      have hfw : f w ≠ 0 := hne w (norm_pos_iff.mpr hw0) hw'
      refine mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hw0)) ?_
      exact sub_ne_zero.mpr (by rw [h0]; exact hfw)
  -- `1/g` is differentiable on the disc and continuous on its closure
  have h1gd : DifferentiableOn ℂ (fun w => (g w)⁻¹) (Metric.ball 0 1) :=
    hgd.inv (fun w hw => hgne w (Metric.ball_subset_closedBall hw))
  have h1gc : ContinuousOn (fun w => (g w)⁻¹) (closure (Metric.ball (0 : ℂ) 1)) := by
    rw [closure_ball 0 hball_ne]
    exact hgc.inv₀ hgne
  have hdc : DiffContOnCl ℂ (fun w => (g w)⁻¹) (Metric.ball 0 1) :=
    DiffContOnCl.mk h1gd h1gc
  -- the boundary bound `‖1/g‖ ≤ c⁻¹`
  have hC : ∀ w ∈ frontier (Metric.ball (0 : ℂ) 1), ‖(g w)⁻¹‖ ≤ c⁻¹ := by
    intro w hw
    rw [frontier_ball 0 hball_ne] at hw
    rw [Metric.mem_sphere] at hw
    have hwn : ‖w‖ = 1 := by rw [dist_eq_norm, sub_zero] at hw; exact hw
    have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hwn; norm_num at hwn
    have hgw : ‖g w‖ = ‖f w‖ := by
      rw [hgdef, dslope_of_ne f hw0, slope_def_module]
      simp only [sub_zero, h0]
      rw [norm_smul, norm_inv, hwn, inv_one, one_mul]
    have hfwpos : 0 < ‖f w‖ := lt_of_lt_of_le hc (hbd w hwn)
    calc ‖(g w)⁻¹‖ = ‖g w‖⁻¹ := norm_inv (g w)
      _ = ‖f w‖⁻¹ := by rw [hgw]
      _ ≤ c⁻¹ := (inv_le_inv₀ hfwpos hc).mpr (hbd w hwn)
  intro z hz
  have hzcl : z ∈ closure (Metric.ball (0 : ℂ) 1) := by
    rw [closure_ball 0 hball_ne, Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hz
  have hzbd := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc hC hzcl
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hz
  have hgz0 : g z ≠ 0 := hgne z hzmem
  have hgzpos : 0 < ‖g z‖ := norm_pos_iff.mpr hgz0
  have hcz : c ≤ ‖g z‖ := by
    rw [norm_inv] at hzbd
    exact (inv_le_inv₀ hgzpos hc).mp hzbd
  have hfz : f z = z * g z := by
    have h := sub_smul_dslope_of_zero h0 z
    rw [sub_zero, ← hgdef] at h
    rw [← h, smul_eq_mul]
  calc c * ‖z‖ ≤ ‖g z‖ * ‖z‖ := mul_le_mul_of_nonneg_right hcz (norm_nonneg z)
    _ = ‖z‖ * ‖g z‖ := by ring
    _ = ‖z * g z‖ := (norm_mul z (g z)).symm
    _ = ‖f z‖ := by rw [hfz]

end Work.CLift
