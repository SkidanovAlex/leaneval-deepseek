import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_rate
import Submission.Work.FTS.EllipticEst.AeI1Fts.cut_deriv_tendsto_zero
import Submission.Work.FTS.EllipticEst.AeI1Fts.hardy_slice_ae
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
-- the proved copy of the statement below
import Submission.Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut.tendsto_terms_cut

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

theorem tendsto_terms_cut {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.U u))
    (hV : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.V u))
    (hA : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.AA u))
    (hB : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.BB u)) :
    (Filter.Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z
        * (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
            * (Work.FTS.EllipticEst.AeI1Fts.AA u z θ * Work.FTS.EllipticEst.AeI1Fts.BB u z θ
                + Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeI1Fts.U u z θ
                  * Work.FTS.EllipticEst.AeI1Fts.BB u z θ))
      Filter.atTop
      (nhds (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * (Work.FTS.EllipticEst.AeI1Fts.AA u z θ * Work.FTS.EllipticEst.AeI1Fts.BB u z θ
                + Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeI1Fts.U u z θ
                  * Work.FTS.EllipticEst.AeI1Fts.BB u z θ))))
  ∧ (Filter.Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0,
        (z * deriv (Work.FTS.EllipticEst.cut k) z) * (Work.Spaces.w z) ^ 2
          * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
            * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.BB u z θ))
      Filter.atTop (nhds 0))
  ∧ (Filter.Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z
        * (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
            * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2)
      Filter.atTop
      (nhds (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.AeI1Fts.sigE θ * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2)))
  ∧ (Filter.Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z
        * (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.AeI1Fts.sig1 θ
            * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
            * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
                * Real.cos (2 * θ)))
      Filter.atTop
      (nhds (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.AeI1Fts.sig1 θ
            * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
                * Real.cos (2 * θ))))) :=
  Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut.tendsto_terms_cut h hU hV hA hB

end Work.FTS.EllipticEst.AeI1Fts
