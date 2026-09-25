/-
# The kernel `W` of the Beurling transform

`W w = (1 - bumpC w) * w⁻²` is the regularised singular kernel that appears in the
definition of the Beurling transform.  Because the cutoff `bumpC` equals `1` on the closed
ball of radius `1/2`, the factor `1 - bumpC` vanishes on that ball and kills the singularity
of `w⁻²` at the origin, so `W` is smooth on all of `ℂ`; outside the unit disc it agrees with
`w⁻²`.

This file records the definition and the elementary evaluation facts.
-/
import Mathlib
import Submission.Work.Beltrami.Cauchy

noncomputable section

namespace Work.Beltrami

open Filter Metric
open scoped Topology
open scoped ContDiff

/-- The regularised Cauchy kernel `W w = (1 - bumpC w) * w⁻²`. -/
def W (w : ℂ) : ℂ := (1 - (bumpC w : ℂ)) * (w ^ 2)⁻¹

@[simp] theorem W_apply (w : ℂ) : W w = (1 - (bumpC w : ℂ)) * (w ^ 2)⁻¹ := rfl

/-- On the closed ball of radius `1/2` the cutoff is `1`, so the kernel vanishes. -/
theorem W_eq_zero_of_norm_le_half {w : ℂ} (h : ‖w‖ ≤ 1 / 2) : W w = 0 := by
  simp [W, bumpC_eq_one h]

/-- Outside the unit disc the cutoff vanishes, so the kernel is `w⁻²`. -/
theorem W_eq_inv_sq_of_one_le {w : ℂ} (h : 1 ≤ ‖w‖) : W w = (w ^ 2)⁻¹ := by
  simp [W, bumpC_eq_zero h]

/-- Near any point of norm `> 1` the kernel agrees with `w⁻²`. -/
theorem W_eventuallyEq_inv_sq {w : ℂ} (h : 1 < ‖w‖) :
    W =ᶠ[𝓝 w] (fun z : ℂ => (z ^ 2)⁻¹) := by
  refine Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds w (by linarith : (0 : ℝ) < ‖w‖ - 1)) ?_
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hbz : bumpC z = 0 := by
    apply bumpC_eq_zero
    have h1 : ‖w‖ ≤ ‖z - w‖ + ‖z‖ := by
      have hle : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
        have hw : (w - z) + z = w := by ring
        calc ‖w‖ = ‖(w - z) + z‖ := (congrArg norm hw).symm
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      rwa [norm_sub_rev] at hle
    linarith
  simp [W, hbz]

/-- The kernel `W` is smooth on all of `ℂ`:  away from `0` it is a product of the smooth
factor `1 - bumpC` with the smooth function `w⁻²`, and near `0` it vanishes identically. -/
theorem W_contDiff : ContDiff ℝ ∞ W := by
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem
      (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 2)) ?_
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    simp [W, bumpC_eq_one hw.le]
  · have hbump : ContDiff ℝ ∞ (fun w : ℂ => (bumpC w : ℂ)) := by
      simpa [Function.comp_def] using Complex.ofRealCLM.contDiff.comp bumpC_contDiff
    have hfac : ContDiffAt ℝ ∞ (fun w : ℂ => (1 : ℂ) - (bumpC w : ℂ)) z :=
      contDiffAt_const.sub hbump.contDiffAt
    have hinv : ContDiffAt ℝ ∞ (fun w : ℂ => (w ^ 2)⁻¹) z :=
      (contDiffAt_id (x := z)).pow 2 |>.inv (by simpa using pow_ne_zero 2 hz)
    exact hfac.mul hinv

end Work.Beltrami
