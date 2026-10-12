import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Basic

open MeasureTheory

/-- The graph point of the zero test function is the zero of the ambient space:
both the `L²` part and every gradient component vanish, since the zero test
function is the zero function and the derivative of a constant function is `0`. -/
theorem graphPoint_zero {N : ℕ} {L : ℝ} :
    graphPoint N L (0 : testSub N L) = 0 := by
  refine Prod.ext ?_ ?_
  · simp only [graphPoint, Submodule.coe_zero]
    exact MeasureTheory.MemLp.toLp_zero _
  · funext j
    simp only [graphPoint, Submodule.coe_zero, fderiv_zero, Pi.zero_apply, zero_apply]
    exact MeasureTheory.MemLp.toLp_zero _

end Work.BoseSym.Basic
