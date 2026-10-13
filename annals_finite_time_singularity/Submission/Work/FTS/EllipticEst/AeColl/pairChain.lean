import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeColl.Defs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.truncZIbp2
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.truncThetaIbpSep
import Submission.Work.FTS.EllipticEst.AeColl.sliceWBound
import Submission.Work.FTS.EllipticEst.AeColl.aeGradTraceRateUnw

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeColl

theorem pairChain : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz →
    (∃ K : ℝ, 0 < K ∧ ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        (z * Work.Spaces.pz u z θ) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo 0 θ, (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig t))
      ∧ (∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        (z * Work.Spaces.pz u z θ) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo θ (Real.pi / 2),
              (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
                * Work.FTS.EllipticEst.AngSecond.sig t))) →
    ∀ n : ℕ,
      ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
          * Work.FTS.EllipticEst.AeColl.Pcut u n
        ≤ Work.FTS.EllipticEst.AeColl.Dcut u n + Work.FTS.EllipticEst.AeColl.Trcut u n
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n := by sorry

end Work.FTS.EllipticEst.AeColl
