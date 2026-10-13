import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.DzAmgm

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The `z`-partial of a `C^{n+1}` function on an open set is `C^n`.**  This is the
finite-order companion of `Work.Spaces.contDiffOn_uncurry_pz` (which is stated for the
analytic order `⊤`); the proof is the same: on an open set `fderivWithin` is `fderiv`, the
Fréchet derivative of a `C^{n+1}` function is `C^n`, and evaluating at the constant direction
`(1,0)` preserves the class. -/
theorem contDiffOn_uncurry_pz_nat {V : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (n : ℕ)
    (h : ContDiffOn ℝ (n.succ) (Function.uncurry V) U) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz V)) U := by
  have hfd := h.fderivWithin (m := n) hU.uniqueDiffOn (by simp)
  have hfd2 : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry V) p) U :=
    hfd.congr fun p hp => (fderivWithin_of_isOpen hU hp).symm
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry V) p) (1, 0)) U :=
    hfd2.clm_apply contDiffOn_const
  refine hcomp.congr fun p hp => ?_
  have hdiff : DifferentiableOn ℝ (Function.uncurry V) U := h.differentiableOn (by simp)
  exact Work.Spaces.pz_eq_fderiv (hdiff.differentiableAt (hU.mem_nhds hp))

theorem ContinuousOnUncurryPzIterTwo {V : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : ContDiffOn ℝ 2 (Function.uncurry V) U) :
    ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 V)) U := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz V)) U :=
    contDiffOn_uncurry_pz_nat hU 1 h
  have h2 : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz V))) U :=
    contDiffOn_uncurry_pz_nat hU 0 h1
  simpa [Work.Spaces.pzIter] using h2.continuousOn

end Work.FTS.EllipticEst.DzAmgm
