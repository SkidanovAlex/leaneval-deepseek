import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Prop.l0_first
import Submission.Work.FTS.EllipticEst.Prop.l0_grad
import Submission.Work.FTS.EllipticEst.TT.weakAngularTermClean
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

open Work.FTS.EllipticEst.TT

/-- The level-`0` estimate of the elliptic chapter, assembled from the four first-order
inputs. -/
theorem level0 : ∃ C : ℝ, 0 < C ∧ EllWeak0 C := by
  obtain ⟨C, hC, h⟩ :=
    L0.l2eta_weak_of_pieces l0_first l0_grad
      (fun C₁ hC₁ => l0_second C₁ hC₁)
      (fun C₁ C_B h1 h2 => weakAngularTermClean C₁ C_B h1 h2)
  exact ⟨C, hC, fun α F Ψ hα hα4 hwk =>
    h α F Ψ hα hα4 hwk.eq hwk.zero hwk.pi_half hwk.orthF hwk.orthPsi hwk.smooth
      hwk.memF hwk.memA hwk.memB hwk.memZPth2⟩

end Work.FTS.EllipticEst.Prop
