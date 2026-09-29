import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.Haupt.haupt_facts
import Submission.Work.CPsi.psiC_facts

/-!
# `t ↦ circleLog phiC t` is continuous on `[0,1]`

`circleLog φ t = log ‖φ (e^{2πit})‖` and `phiC` is the contour map of Theorem C,
`phiC = hauptH ∘ psiC`.  The function `t ↦ circleLog phiC t` is the composition of

* the continuous parametrisation `t ↦ e^{2πit}`, which lands in the closed unit disc, on which
  `phiC` is continuous, and
* `log ‖·‖`, which is continuous on `{0}ᶜ`.

`phiC` does not vanish on the unit circle: `psiC` maps the closed disc into `closedBall 0 (3/4)`,
on which `hauptH` vanishes only at `0` (`Work.Haupt.hauptH_ne_zero`), and `psiC z = 0` forces
`z = 0` (`Work.CPsi.psiC_eq_zero`), while `|e^{2πit}| = 1 ≠ 0`.

Only the `sorry`-free parts of the `Haupt`/`PsiC` facts are used here: the bundled `HauptFacts`
(whose proof still contains a `sorry` for the holomorphic square root of `h - 4`) is deliberately
avoided.
-/

namespace Work.CNum

open Complex Metric Filter Topology
open scoped BigOperators

/-- `phiC = hauptH ∘ psiC` is continuous on the closed unit disc: `psiC` maps it into
`closedBall 0 (3/4)`, on which `hauptH` is continuous (it is holomorphic on the larger ball
`ball 0 1`). -/
theorem phiC_continuousOn_closedBall :
    ContinuousOn Submission.CDTPlan.phiC (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨hPcont, -, -, -, hPbound, -⟩ := Work.CPsi.psiC_facts
  have hHcont : ContinuousOn Submission.CDTPlan.hauptH (Metric.closedBall (0 : ℂ) (3 / 4)) := by
    apply continuousOn_of_forall_continuousAt
    intro q hq
    have hqn : ‖q‖ ≤ 3 / 4 := by simpa [Metric.mem_closedBall, dist_zero_right] using hq
    have hq1 : q ∈ Metric.ball (0 : ℂ) 1 := by
      simp only [Metric.mem_ball, dist_zero_right]
      linarith
    exact (Work.Haupt.differentiableOn_hauptH.differentiableAt
      (isOpen_ball.mem_nhds hq1)).continuousAt
  have hcomp : ContinuousOn (fun z => Submission.CDTPlan.hauptH (Submission.CDTPlan.psiC z))
      (Metric.closedBall (0 : ℂ) 1) :=
    hHcont.comp hPcont (fun z hz => by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact hPbound z hz)
  exact hcomp

/-- The parametrisation of the unit circle used by `circleLog`. -/
private noncomputable def circParam (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))

private lemma continuous_circParam : Continuous circParam := by
  change Continuous (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))
  fun_prop

private lemma norm_circParam (t : ℝ) : ‖circParam t‖ = 1 := by
  rw [circParam]
  rw [Complex.norm_exp]
  simp

private lemma circParam_ne_zero (t : ℝ) : circParam t ≠ 0 := by
  intro h
  have h1 := norm_circParam t
  rw [h, norm_zero] at h1
  norm_num at h1

/-- `phiC` has no zero on the unit circle. -/
private lemma phiC_ne_zero_on_circle (t : ℝ) : Submission.CDTPlan.phiC (circParam t) ≠ 0 := by
  intro hzero
  have hψmem : Submission.CDTPlan.psiC (circParam t) ∈ Metric.ball (0 : ℂ) 1 := by
    have h1 : ‖Submission.CDTPlan.psiC (circParam t)‖ ≤ 3 / 4 :=
      Work.CPsi.psiC_norm_le (le_of_eq (norm_circParam t))
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hψ0 : Submission.CDTPlan.psiC (circParam t) = 0 :=
    Work.Haupt.hauptH_ne_zero _ hψmem (by simpa [Submission.CDTPlan.phiC] using hzero)
  exact circParam_ne_zero t (Work.CPsi.psiC_eq_zero hψ0)

theorem continuousOn_circleLog :
    ContinuousOn (fun t : ℝ => Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t) (Set.Icc 0 1) := by
  have hφcont : ContinuousOn Submission.CDTPlan.phiC (Metric.closedBall (0 : ℂ) 1) :=
    phiC_continuousOn_closedBall
  have hmaps : Set.MapsTo circParam (Set.Icc 0 1) (Metric.closedBall (0 : ℂ) 1) := by
    intro t _
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [norm_circParam t]
  have hcomp : ContinuousOn (fun t : ℝ => Submission.CDTPlan.phiC (circParam t))
      (Set.Icc 0 1) :=
    hφcont.comp continuous_circParam.continuousOn hmaps
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Submission.CDTPlan.phiC (circParam t)‖ ≠ 0 := by
    intro t _
    rw [norm_ne_zero_iff]
    exact phiC_ne_zero_on_circle t
  have hlog := hcomp.norm.log hne
  simpa [Submission.CDTPlan.circleLog, circParam] using hlog

end Work.CNum
