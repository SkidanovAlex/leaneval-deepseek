import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.FTS.EllipticEst.TT.interpGamma_core_compact
import Submission.Work.FTS.EllipticEst.TT.radialIBPOpen
import Submission.Work.FTS.EllipticEst.TT.sliceIBPLight
import Submission.Work.FTS.EllipticEst.TT.sliceRate_light

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

theorem interpGammaCoreFts : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen G →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 G) →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iz →
      Work.FTS.EllipticEst.TT.Xint α G
        ≤ C * (Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
              * Work.FTS.EllipticEst.TT.TTint α G)
            + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) := by
  sorry

end Work.FTS.EllipticEst.TT
