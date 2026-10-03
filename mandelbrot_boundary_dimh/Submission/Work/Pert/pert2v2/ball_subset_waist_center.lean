import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.Gates
import Submission.Work.Pert.waist_low

namespace Work.Pert.pert2v2

open _root_.MandelDim Complex Set Metric

/-!
# `pert2v2.ball_subset_waist_center`

The **waist** of §4.2, `Qm ξ α ∩ Qp ξ α`, is the symmetric horizontal window
`{z | |z.re| < |z.im| - ξ}` (`Work.Pert.Qm_inter_Qp`, which uses `MandelDim.InF1 α` through
`Work.Pert.abs_im_one_div_lt_re_one_div`).  Here we record that a ball centred at a point `w`
with `|w.re| < 1`, `|w.im| = T` and `1 + Ξ ≤ T/2` — i.e. `T ≳ 2(Ξ + 1)`, the height at which
the two gates have opened — lies inside the waist with room to spare: its radius `T/4` is
strictly less than the waist half-width `|w.im| - Ξ - |w.re| ≥ T - Ξ - 1 - T/4 ≥ 3T/4` at the
centre, and on the ball `|Re z| < 1 + T/4`, `|Im z| > T - T/4 = 3T/4`.

Hence every `z` of the ball satisfies `|z.re| < 1 + T/4 < 3T/4 < |z.im| - Ξ`, which is exactly
membership in `Qm Ξ α ∩ Qp Ξ α`.  (Nothing is assumed about the sign of `T`: if `T ≤ 0` the
ball is empty.) -/
theorem ball_subset_waist_center {Ξ T : ℝ} {α w : ℂ} (hF1 : MandelDim.InF1 α)
    (hre : |w.re| < 1) (him : |w.im| = T) (hT : 1 + Ξ ≤ T / 2) :
    Metric.ball w (T / 4) ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α := by
  rw [Work.Pert.Qm_inter_Qp (Work.Pert.abs_im_one_div_lt_re_one_div hF1)]
  intro z hz
  change |z.re| < |z.im| - Ξ
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hre_le : |z.re - w.re| ≤ ‖z - w‖ := by
    simpa using Complex.abs_re_le_norm (z - w)
  have him_le : |z.im - w.im| ≤ ‖z - w‖ := by
    simpa using Complex.abs_im_le_norm (z - w)
  -- `z` stays in the horizontal strip `|Re z| < 1 + T/4`
  have hA : |z.re| < 1 + T / 4 := by
    have h2 : |z.re| ≤ |w.re| + |z.re - w.re| := by
      have h := abs_sub_abs_le_abs_sub z.re w.re
      linarith
    linarith
  -- `z` stays above the height `3T/4 > Ξ + 1 + T/4`
  have hB : Ξ + 1 + T / 4 < |z.im| := by
    have h2 : |w.im| - |z.im - w.im| ≤ |z.im| := by
      have h := abs_sub_abs_le_abs_sub w.im z.im
      rw [abs_sub_comm w.im z.im] at h
      linarith
    rw [him] at h2
    linarith
  rw [abs_lt]
  constructor <;> linarith [neg_abs_le z.re, le_abs_self z.re]

end Work.Pert.pert2v2
