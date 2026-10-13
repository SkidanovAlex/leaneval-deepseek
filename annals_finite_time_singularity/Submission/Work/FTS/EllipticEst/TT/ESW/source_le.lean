import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.Cores.Pieces.TopSlotRhsDom

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT.ESW

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# `source_le`

The top plain angular slot of the source `Gsl α F Ψ = F + α²·Asl Ψ + α(5+α)·D_zΨ` of the
sliced equation is dominated by `C·HkSq α k F`, for `k ≥ 3`, `0 < α ≤ 1/4`, under the two
level-`(k-1)` bounds on `(Asl Ψ, Bsl Ψ)` and on `(Asl (D_zΨ), Bsl (D_zΨ))`.

## Proof

The source `Gsl α F Ψ` is the function `Work.FTS.EllipticEst.Mine.Gsrc α F Ψ` (they are equal
by `gsrc_eq_gsl` below, both being
`(z,θ) ↦ F z θ + α²·(z²∂_z²Ψ z θ) + α(5+α)·(z∂_zΨ z θ)`), and the two hypotheses of the
statement are literally `Cores.Pieces.H1 D α k F Ψ` and `Cores.Pieces.H2 D α k F Ψ`.  The
top-slot bound asked for is therefore exactly

  `Work.FTS.EllipticEst.Cores.Pieces.topSrcSlot D hD k hk`

(a proved, axiom-clean lemma of that module: it splits `∂_θ^k(Gsrc α F Ψ)` into the three
summands `∂_θ^k F`, `α²∂_θ^k(z²∂_z²Ψ)`, `α(5+α)∂_θ^k(D_zΨ)`, bounds the first by the slots of
`HkSq α k F`, the second by hypothesis `H1` at levels `≤ k-1` together with the top `D_θ^k`-slot
`A_top_slot_bound`, and the third by hypothesis `H2` through `∂_θθ(D_zΨ)`), and the proof below
is the reduction of the statement to it.

The auxiliary module `ESW.SourceAux` contains the lemmas that were developed for the direct
route (the `F`-piece `srcF`, the smoothness of `F`/`D_zΨ`/`z²∂_z²Ψ`/`∂_θ²Ψ` on the open
quadrant, the pointwise/integrated top-slot bounds `slot_top_le_HkIntegrand` /
`slot_top_integral_le`, and the triangular comparison `reverse_expansion_sq`); they are
independent of this reduction.
-/

/-- `Gsrc` (the notation of `Cores.Pieces`) and `Gsl` (the notation of this file) are the same
function. -/
theorem gsrc_eq_gsl (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.Mine.Gsrc α F Ψ = Gsl α F Ψ := by
  funext z θ
  simp only [Work.FTS.EllipticEst.Mine.Gsrc, Gsl, Asl, Work.Spaces.Dz]

theorem source_le (D : ℝ) (hD : 0 < D) :
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
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Cores.Pieces.topSrcSlot D hD k hk
  refine ⟨C, hCpos, fun α F Ψ hα hα4 hwk h1 h2 => ?_⟩
  have h := hC α F Ψ hα hα4 hwk h1 h2
  simpa only [gsrc_eq_gsl α F Ψ] using h

end

end Work.FTS.EllipticEst.TT.ESW
