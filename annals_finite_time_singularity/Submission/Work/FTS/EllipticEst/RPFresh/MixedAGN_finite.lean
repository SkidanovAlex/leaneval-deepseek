import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RPFresh

theorem MixedAGN_finite (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (G : ℝ → ℝ → ℝ)
    (hG : Work.FTS.EllipticEst.SmoothOpen G) (hvan : Work.Spaces.VanishTheta G)
    (hdd : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz)
    (htt : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz)
    (hd : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz)
    (hdec : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
      (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz := by sorry

end Work.FTS.EllipticEst.RPFresh
