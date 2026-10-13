import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.pointwise_ident
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.AeI1Fts.hardy_N
import Submission.Work.FTS.EllipticEst.AeI1Fts.hardy_slice_ae
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_rate
import Submission.Work.FTS.EllipticEst.AeI1Fts.cut_deriv_tendsto_zero
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
-- import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_theta_ibp_cut
-- import Submission.Work.FTS.EllipticEst.AeI1Fts.iter_swap_compact
-- import Submission.Work.FTS.EllipticEst.AeI1Fts.psiDeriv_tendsto_zero
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
-- the assembled proof of the (identical) statement `radial_identity_alt`
import Submission.Work.FTS.EllipticEst.AeI1Fts.radial_alt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "χ" => Work.FTS.EllipticEst.cut
local notation "ψ" => Work.FTS.EllipticEst.SliceMixedAux.cut

/-- On the two transition windows of the angular cut-off `ψ ε`, the angular weight
`σ = sigE = sin(2θ)^{-η}` is dominated by `16 ε ^ 2` times the `N`-weight
`sig2 θ * cos(2θ)^2`; indeed `σ = tan(2θ)^2 · sig2 · cos^2(2θ)` and `|tan(2θ)| ≤ 4 ε`
on both windows (for `ε ≤ π/8`). -/
theorem sigE_mul_le_window {ε θ : ℝ} (hε : 0 < ε) (hε8 : ε ≤ Real.pi / 8)
    (h : θ ∈ Set.Ioc (ε / 2) ε ∪ Set.Icc (Real.pi / 2 - ε) (Real.pi / 2 - ε / 2))
    (f : ℝ) :
    sigE θ * f ^ 2 ≤ 16 * ε ^ 2 * (sig2 θ * f ^ 2 * (Real.cos (2 * θ)) ^ 2) := by
  sorry

theorem radial_identity {α : ℝ} {u G : ℝ → ℝ → ℝ}
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

end

end Work.FTS.EllipticEst.AeI1Fts
