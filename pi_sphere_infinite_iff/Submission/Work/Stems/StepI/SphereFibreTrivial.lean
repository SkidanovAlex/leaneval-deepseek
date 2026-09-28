import Submission.Work.Stems.StepI.FibrewiseTrivialPath
import Submission.Work.StemsB.serreSphere_contract_big
import Submission.Work.StemsB.SerreSphereStep
import Submission.Work.StemsB.WangSphereHomology

/-!
# The fibrewise triviality of the path–loop fibration over the two pieces of the sphere model

The two-piece decomposition of `SphModel n = OnePoint ℝⁿ` used by Step I and by the Wang chapter is

* `sphLoopThick n` / `sphLoopOuter n` (the outer thickening of the outer disc, containing `∞`), and
* `sphLoopBig n = {|v|_∞ < 3/2}` (the inner cube),

with `sphLoopOuter n ∪ sphLoopBig n = univ` and intersection the collar `sphLoopCollar n`.

Both pieces carry an explicit based contraction (`sphLoopOuterContr n` to `∞`, and the affine
contraction of `sphLoopBig n` to the shell point `sphShellPt n`), so both satisfy the hypothesis of
`Work.Stems.StepI.fibrewiseTrivial_of_contraction`; this file records the two resulting instances of
`Work.StemsB.FibrewiseTrivial` for the path–loop fibration `evalOne (SphModel n) ∞`.

This is the missing input of `Work.StemsB.wangTauSphere`, `Work.StemsB.wangHomExactSphere` and of
Step I of the sphere-specific route.
-/

open scoped Topology unitInterval
open Work.StemsB

namespace Work.Stems.StepI

noncomputable section

theorem fibrewiseTrivial_sphLoopOuter (n : ℕ) :
    FibrewiseTrivial (evalOne (SphModel n) OnePoint.infty) (sphLoopOuter n) (dOuter n) := by
  refine fibrewiseTrivial_of_contraction (d₀ := OnePoint.infty)
    (infty_subset_outer n rfl) (sphLoopOuterContr n) (sphLoopOuterContr_zero n) ?_
  intro w
  exact sphLoopOuterContr_one n w

theorem fibrewiseTrivial_sphLoopBig (n : ℕ) (hn : 1 ≤ n) (hc : sphShellPt n ∈ sphLoopBig n) :
    FibrewiseTrivial (evalOne (SphModel n) OnePoint.infty) (sphLoopBig n) ⟨sphShellPt n, hc⟩ := by
  obtain ⟨c, hc0, hc1, -⟩ := serreSphere_contract_big n hn hc
  exact fibrewiseTrivial_of_contraction hc c hc0 hc1

theorem fibrewiseTrivial_sphLoopBig' (n : ℕ) (hn : 1 ≤ n) :
    FibrewiseTrivial (evalOne (SphModel n) OnePoint.infty) (sphLoopBig n)
      ⟨sphShellPt n, (sphShellPt_mem_sphLoopCollar n hn).2⟩ :=
  fibrewiseTrivial_sphLoopBig n hn (sphShellPt_mem_sphLoopCollar n hn).2

end

end Work.Stems.StepI
