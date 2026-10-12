import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Basic

open MeasureTheory Filter

theorem graphPoint_add {N : ℕ} {L : ℝ} (F G : testSub N L) :
    graphPoint N L (F + G) = graphPoint N L F + graphPoint N L G := by
  apply Prod.ext
  · -- the function part: `toLp` of a sum is the sum of the `toLp`s
    simp only [graphPoint, Prod.fst_add]
    refine (MemLp.toLp_congr _ _ ?_).trans (MemLp.toLp_add _ _)
    rw [Submodule.coe_add]
  · -- the gradient part: the derivative is additive and `toLp` is additive
    simp only [graphPoint, Prod.snd_add]
    funext j
    simp only [Pi.add_apply]
    set d : Conf N := Submission.BoseGases.kcDir N j.1 j.2 with hd
    have hder : (fun x : Conf N => fderiv ℝ ((F + G : testSub N L) : Conf N → ℝ) x d)
        = (fun x : Conf N => fderiv ℝ (F : Conf N → ℝ) x d)
          + (fun x : Conf N => fderiv ℝ (G : Conf N → ℝ) x d) := by
      funext x
      rw [Pi.add_apply, Submodule.coe_add, fderiv_add]
      · rfl
      · exact (F.2.1.differentiable (by simp)).differentiableAt
      · exact (G.2.1.differentiable (by simp)).differentiableAt
    refine (MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq hder)).trans (MemLp.toLp_add _ _)

end Work.BoseSym.Basic
