import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeColl.Defs
import Submission.Work.FTS.EllipticEst.H2W.SlotA.cwPairBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeColl

theorem limitBound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz →
    (∀ n : ℕ,
      ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
          * Work.FTS.EllipticEst.AeColl.Pcut u n
        ≤ Work.FTS.EllipticEst.AeColl.Dcut u n + Work.FTS.EllipticEst.AeColl.Trcut u n
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n) →
    ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
        * Work.FTS.EllipticEst.AeColl.Vfull u
      ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
            (Work.Spaces.pthIter 2 u)
        + C * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
              (Work.FTS.EllipticEst.AeColl.Uz u)
            + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
                (Work.FTS.EllipticEst.AeColl.Uz u))
              * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u))) := by sorry

end Work.FTS.EllipticEst.AeColl
