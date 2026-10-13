import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.pointwise_ident
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_theta_ibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.hardy_slice_ae
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_rate
-- the assembled proof of the (identical) statement `radial_identity_alt`
import Submission.Work.FTS.EllipticEst.AeI1Fts.radial_alt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

theorem radial_identity2 {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.U u))
    (hV : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.V u))
    (hA : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.AA u))
    (hB : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.BB u)) :
    Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeI1Fts.AA u)
        (Work.FTS.EllipticEst.AeI1Fts.BB u)
      + Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AeI1Fts.U u z θ)
          (Work.FTS.EllipticEst.AeI1Fts.BB u)
      = (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2
                  * Work.FTS.EllipticEst.AeI1Fts.sigE θ)
        - 2 * Work.Spaces.eta
            * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
                * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                    Work.FTS.EllipticEst.AeI1Fts.U u z θ
                      * Work.FTS.EllipticEst.AeI1Fts.V u z θ * Real.cos (2 * θ)
                      * Work.FTS.EllipticEst.AeI1Fts.sig1 θ) :=
  radial_identity_alt h hU hV hA hB

end Work.FTS.EllipticEst.AeI1Fts
