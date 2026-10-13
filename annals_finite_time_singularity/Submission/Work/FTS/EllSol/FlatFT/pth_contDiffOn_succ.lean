import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

/-- The curried `θ`-partial derivative `∂_θ G` of a function which is `C^{n+1}` on an open
set is `C^n` on that set.  (The `⊤`-version is `Work.Spaces.contDiffOn_uncurry_pth`.) -/
theorem pth_contDiffOn_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  -- the Fréchet derivative of `uncurry G` is `C^n` on `V`
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := (n : WithTop ℕ∞)) hV.uniqueDiffOn (by simp)
    refine h'.congr fun p hp => ?_
    rw [fderivWithin_of_isOpen hV hp]
  -- evaluate it in the direction `(0,1)`
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ n (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)) V)
  -- identify `∂_θ G` with that evaluation of the Fréchet derivative
  refine hcomp.congr fun p hp => ?_
  have hdiff : DifferentiableAt ℝ (Function.uncurry G) p :=
    (h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp)
  simp only [Function.uncurry]
  exact Work.Spaces.pth_eq_fderiv hdiff

end Work.FTS.EllSol.FlatFT
