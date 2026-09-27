import Mathlib
import Submission.Work.EQ.CayleyUHPDefs

noncomputable section

open scoped Manifold Topology
open Filter Metric

namespace Work.EQ

theorem cayleyUHP_mdifferentiableAt {z : ℂ} (hz : ‖z‖ < 1) :
    MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      Work.EQ.cayleyUHP z := by
  have hzb : z ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball, dist_eq_norm, sub_zero] using hz
  have hev : cayleyUHP =ᶠ[𝓝 z] (fun w => UpperHalfPlane.ofComplex (cayley w)) := by
    refine eventually_of_mem (isOpen_ball.mem_nhds hzb) ?_
    intro w hw
    have hw' : ‖w‖ < 1 := by simpa [mem_ball, dist_eq_norm, sub_zero] using hw
    rw [cayleyUHP_eq hw']
    exact (UpperHalfPlane.ofComplex_apply_of_im_pos (cayley_im_pos hw')).symm
  have hcay :
      MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) cayley z := by
    have hd : DifferentiableAt ℂ cayley z := by
      unfold cayley
      exact DifferentiableAt.div
        (DifferentiableAt.mul (differentiableAt_const Complex.I)
          (DifferentiableAt.add (differentiableAt_const 1) differentiableAt_id))
        (DifferentiableAt.sub (differentiableAt_const 1) differentiableAt_id)
        (one_sub_ne_zero hz)
    exact hd.mdifferentiableAt
  exact MDifferentiableAt.congr_of_eventuallyEq
    (MDifferentiableAt.comp z (UpperHalfPlane.mdifferentiableAt_ofComplex (cayley_im_pos hz)) hcay)
    hev

end Work.EQ
