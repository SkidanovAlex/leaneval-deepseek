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

namespace Work.Spaces

theorem uncurry_partial_c1 {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ 2 (Function.uncurry G) V) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz G)) V ∧
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth G)) V := by
  have hdiff : ∀ p ∈ V, DifferentiableAt ℝ (Function.uncurry G) p := fun p hp =>
    (h.differentiableOn (n := 2) (by norm_num)).differentiableAt (hV.mem_nhds hp)
  have hfd : ContDiffOn ℝ 1 (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := 1) hV.uniqueDiffOn (by norm_num)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hfd1 : ContDiffOn ℝ 1
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  have hfd2 : ContDiffOn ℝ 1
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  refine ⟨?_, ?_⟩
  · refine hfd1.congr ?_
    intro p hp
    exact pz_eq_fderiv (hdiff p hp)
  · refine hfd2.congr ?_
    intro p hp
    exact pth_eq_fderiv (hdiff p hp)

end Work.Spaces
