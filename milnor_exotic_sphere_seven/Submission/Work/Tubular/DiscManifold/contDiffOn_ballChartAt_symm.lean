import Mathlib
import Submission.Work.Tubular.DiscManifold.Defs
import Submission.Work.SignatureBordism.BallBoundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology

/-!
# Smoothness of the inverse of the preferred chart of the closed ball

The preferred chart `chartAt (Half n) b` of the closed ball `Ball n = D^{n+1}` at a point `b`
(`Work.SignatureBordism.ballChartedSpace`) is either

* the centre chart `interiorChart n`, whose inverse formula is the affine map `y ↦ y - (1/2) e₀`,
  or
* a half-ball chart `halfChart n i ε`, whose inverse formula is the explicit radial formula
  `halfInvRawE n i ε`,
  `y ↦ permIso i (consCLM (ε * sqrt ((1 - y 0)^2 - ‖tail y‖^2), tail y))`.

Both formulas are smooth on the chart target (`contDiffOn_halfInvRawE` for the second one, where
the square-root argument is non-zero — it is even positive by `halfTarget_g_pos`).  Reading the
inverse chart on the model space — i.e. composing with `(hModel n).symm`, which on the half-space
`{w | 0 ≤ w 0}` is just the subtype inclusion — this gives the smoothness of

`w ↦ ((chartAt (Half n) b).symm ((hModel n).symm w)).val`

on `{w | 0 ≤ w 0 ∧ (hModel n).symm w ∈ (chartAt (Half n) b).target}`.

This is the companion of `Work.Tubular.DiscManifold.contDiffOn_ballChartAt` (the forward chart
read on the model space), and is one of the analytic inputs of the tubular-neighbourhood
construction of the disc manifold.
-/

namespace Work.Tubular.DiscManifold

open Work.SignatureBordism

/-- **Smoothness of the inverse of the centre chart on the model space.**  On the half-space the
chart inverse is the affine map `w ↦ w - shiftE n`. -/
theorem contDiffOn_interiorChart_symm_model (n : ℕ) :
    ContDiffOn ℝ 1
      (fun w : EuclideanSpace ℝ (Fin (n + 1)) =>
        (((interiorChart n).symm ((hModel n).symm w) : Ball n).val))
      {w : EuclideanSpace ℝ (Fin (n + 1)) |
        0 ≤ w 0 ∧ (hModel n).symm w ∈ (interiorChart n).target} := by
  have h : ContDiffOn ℝ 1 (fun w : EuclideanSpace ℝ (Fin (n + 1)) => w - shiftE n) Set.univ := by
    have h2 : ContDiff ℝ 1 (fun w : EuclideanSpace ℝ (Fin (n + 1)) => w - shiftE n) := by fun_prop
    exact h2.contDiffOn
  refine (h.mono (Set.subset_univ _)).congr ?_
  intro w hw
  rw [interiorChart_symm_apply n hw.2, interiorInvRawE]
  exact congrArg (fun v => v - shiftE n)
    (congrArg Subtype.val (halfModel_symm_apply_of_le n hw.1))

/-- **Smoothness of the inverse of a half-ball chart on the model space.**  On the half-space the
chart inverse is the explicit radial formula `halfInvRawE n i ε`, which is smooth wherever its
square-root argument is non-zero; on the chart target it is strictly positive. -/
theorem contDiffOn_halfChart_symm_model (n : ℕ) (i : Fin (n + 1)) (ε : Bool) :
    ContDiffOn ℝ 1
      (fun w : EuclideanSpace ℝ (Fin (n + 1)) =>
        (((halfChart n i ε).symm ((hModel n).symm w) : Ball n).val))
      {w : EuclideanSpace ℝ (Fin (n + 1)) |
        0 ≤ w 0 ∧ (hModel n).symm w ∈ (halfChart n i ε).target} := by
  refine ContDiffOn.congr
    (f := fun w : EuclideanSpace ℝ (Fin (n + 1)) => halfInvRawE n i ε w) ?_ ?_
  · refine ((contDiffOn_halfInvRawE n i ε).mono ?_).of_le le_top
    intro w hw
    have hco : ((hModel n).symm w).val = w :=
      congrArg Subtype.val (halfModel_symm_apply_of_le n hw.1)
    have hg := halfTarget_g_pos n hw.2
    rw [hco] at hg
    simpa using hg.ne'
  · intro w hw
    rw [halfChart_symm_apply n i ε hw.2]
    exact congrArg (fun v => halfInvRawE n i ε v)
      (congrArg Subtype.val (halfModel_symm_apply_of_le n hw.1))

theorem contDiffOn_ballChartAt_symm (n : ℕ) (b : Work.SignatureBordism.Ball n) :
    ContDiffOn ℝ 1
      (fun w : EuclideanSpace ℝ (Fin (n + 1)) =>
        (((chartAt (Work.SignatureBordism.Half n) b).symm ((Work.SignatureBordism.hModel n).symm w) : Work.SignatureBordism.Ball n).val))
      {w : EuclideanSpace ℝ (Fin (n + 1)) |
        0 ≤ w 0 ∧ (Work.SignatureBordism.hModel n).symm w ∈ (chartAt (Work.SignatureBordism.Half n) b).target} := by
  rw [show chartAt (Half n) b = ballChartAt n b from rfl]
  by_cases hb : b ∈ interiorSource n
  · rw [ballChartAt_of_mem n hb]
    exact contDiffOn_interiorChart_symm_model n
  · rw [ballChartAt_of_not_mem n hb]
    exact contDiffOn_halfChart_symm_model n (ballCoord n b (ball_ne_zero_of_not_mem n hb))
      (decide (0 < (b : EuclideanSpace ℝ (Fin (n + 1)))
        (ballCoord n b (ball_ne_zero_of_not_mem n hb))))

end Work.Tubular.DiscManifold
