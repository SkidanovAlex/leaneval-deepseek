import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs
import Submission.Work.FTS.EllipticEst.TT.ESW.SourceAux
import Submission.Work.FTS.EllipticEst.TT.ESW.low_order_split
import Submission.Work.FTS.EllipticEst.TT.ESW.low_order_le
import Submission.Work.FTS.EllipticEst.remov.HkSq_step_le
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.ATopClean
import Submission.Work.FTS.EllipticEst.Cores.Pieces.TopSlotRhsDom

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.Rtilde

open scoped Real Topology

/-- The source `Gsrc` of `Mine.SlotDefs` (used by the proved top-slot bound
`Cores.Pieces.topSrcSlot`) and the source `Gsl` of `TT.ESW.Defs` are the same function:
both are `(z,θ) ↦ F z θ + α²·(z²∂_z²Ψ) + α(5+α)·(z∂_zΨ)`. -/
theorem gsrc_eq_gsl (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.Mine.Gsrc α F Ψ = Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ := by
  funext z θ
  simp only [Work.FTS.EllipticEst.Mine.Gsrc, Work.FTS.EllipticEst.TT.ESW.Gsl,
    Work.FTS.EllipticEst.TT.ESW.Asl, Work.Spaces.Dz]

-- The angular source slot of the induction step of Elgindi's `prop:Hk` (verbatim copy of the
-- statement of `Submission/Work/FTS/EllipticEst/TT/ESW/source_le.lean`, which is `sorry`).
-- `Gsl α F Ψ = F + α²·Asl Ψ + α(5+α)·D_zΨ` is the angular source of the sliced equation
-- (`ESW.Defs.slice_source_eq`, PROVED), so the integrand splits pointwise into the three pieces
-- `∂_θ^k F`, `α²∂_θ^k(Asl Ψ)` and `α(5+α)∂_θ^k(D_z Ψ)`.  The F-piece is
-- `Work.FTS.EllipticEst.TT.ESW.srcF` (PROVED), the `Asl`-piece is
-- `Work.FTS.EllipticEst.remov.A_top_slot_bound` (PROVED: `α²√(Tk α k A) ≤ C|F|_k`) together with
-- `Work.FTS.EllipticEst.remov.HkSq_step_le` (PROVED), and the `D_zΨ`-piece is the triangular
-- comparison `Work.FTS.EllipticEst.TT.ESW.reverse_expansion_sq` (PROVED) with the η-weighted
-- `D_θ`-slots of `D_z(Bsl Ψ) = D_zB` supplied by hypothesis (2).  See the module docstring of
-- `TT/ESW/source_le.lean` for the exact route.
theorem SourceLe (D : ℝ) (hD : 0 < D) :
    ∀ (k : ℕ), 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Asl Ψ)
          + Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Asl (Work.Spaces.DzIter 1 Ψ))
          + Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkSq α k F := by
  intro k hk
  -- The two hypotheses are exactly `Cores.Pieces.H1`/`H2` (the abbreviations `Asl`, `Bsl`
  -- unfold to the expressions appearing in them), and the top-slot bound of `topSrcSlot`
  -- is proved there for the same source `Gsrc = Gsl`.
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Cores.Pieces.topSrcSlot D hD k hk
  refine ⟨C, hCpos, fun α F Ψ hα hα4 hwk h1 h2 => ?_⟩
  have h := hC α F Ψ hα hα4 hwk h1 h2
  simpa only [gsrc_eq_gsl α F Ψ] using h

end Work.FTS.EllipticEst.Prop.Rtilde
