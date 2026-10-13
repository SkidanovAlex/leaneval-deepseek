import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut.TTAuxLimit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts.TendstoTermsCut.tendsto_terms_cut`

The four `k → ∞` limits of the doubly truncated `I₁` identity, assembled from
`AeI1Fts.TendstoTermsCut.tendsto_AB`, `tendsto_dchi`, `tendsto_Vsq` and `tendsto_sig1`
(module `...TendstoTermsCut.TTAuxLimit`), whose `II`-forms are definitionally the statements
below (with `dk k = 1/((k:ℝ)+1)`).
-/

namespace Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut

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
                * Real.cos (2 * θ))))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [dk] using tendsto_AB h hU hV hA hB
  · simpa only [dk] using tendsto_dchi h hU hV hA hB
  · simpa only [dk] using tendsto_Vsq h hU hV hA hB
  · simpa only [dk] using tendsto_sig1 h hU hV hA hB

end Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut
