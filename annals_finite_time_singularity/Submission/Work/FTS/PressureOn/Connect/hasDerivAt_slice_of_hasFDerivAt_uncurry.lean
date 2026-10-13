import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem hasDerivAt_slice_of_hasFDerivAt_uncurry {v : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {x : Work.FTS.PressureOn.R3} {t : ℝ}
    (h : HasFDerivAt (Function.uncurry v) (fderiv ℝ (Function.uncurry v) (x, t)) (x, t)) :
    HasDerivAt (fun s => v x s) ((fderiv ℝ (Function.uncurry v) (x, t)) (0, 1)) t := by
  have hslice : HasFDerivAt (fun s : ℝ => (x, s))
      (ContinuousLinearMap.inr ℝ Work.FTS.PressureOn.R3 ℝ) t :=
    hasFDerivAt_prodMk_right x t
  have hcomp := h.comp t hslice
  have hd := hcomp.hasDerivAt
  simp only [ContinuousLinearMap.comp_apply] at hd
  exact hd

end Work.FTS.PressureOn.Connect
