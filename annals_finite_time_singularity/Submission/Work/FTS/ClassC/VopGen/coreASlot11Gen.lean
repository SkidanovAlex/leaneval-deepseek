import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.H2W.AeDataAof
import Submission.Work.FTS.EllipticEst.Prop.aslotTwoShift
import Submission.Work.FTS.EllipticEst.Prop.mixedSlotInterpEta
import Submission.Work.FTS.EllipticEst.Prop.radialIbpWild
import Submission.Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.sliceAgmonVanishing
import Submission.Work.FTS.EllipticEst.Prop.zIbpTwoD
import Submission.Work.FTS.EllipticEst.Prop.thetaIbpTwoD
import Submission.Work.FTS.EllipticEst.Mine.Auxiliary.cutoffFamilyMonoSmooth
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.FTS.ClassC.VopGen.CoreSplit
import Submission.Work.FTS.ClassC.VopGen.sliceAgmonAofGen
import Submission.Work.FTS.ClassC.VopGen.Core.truncProof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.VopGen

theorem coreASlot11Gen :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ K * ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
                * (Work.Spaces.w z) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ) ^ 2
                * (Work.Spaces.w z) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ) ^ 2
                * (Work.Spaces.w z) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) :=
  coreASlot11_of_pieces sliceAgmonAofGen Core.truncProof

end Work.FTS.ClassC.VopGen
