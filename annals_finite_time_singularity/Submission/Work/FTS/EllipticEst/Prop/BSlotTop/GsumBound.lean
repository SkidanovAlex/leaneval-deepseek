/-
Work module for the Elgindi finite-time singularity project.

# `BSlotTop/GsumBound`: the source slot bounded by `HkSq α k F`

This is the clean-cone copy of `Work.FTS.EllipticEst.remov.TopCoreB.Gsum_bound`
(`Submission/Work/FTS/EllipticEst/remov/TopCoreB/BHalfClean.lean`), with the `sorry`-carrying
`remov.TopCoreB.srcBound` replaced by the proved sibling `BSlotTop.srcBoundFts`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.ATopClean
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs
import Submission.Work.FTS.EllipticEst.Prop.BSlotTop.SrcBoundFts
import Submission.Work.FTS.EllipticEst.Prop.BSlotTop.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.BSlotTop

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The source slot bounded by `HkSq α k F` alone**, from `srcBoundFts` (the reduction form),
the `A`-slot bound `A_top_slot_bound`, and the two hypotheses of the induction step. -/
theorem Gsum_bound_fts (D : ℝ) (hD : 0 < D) :
    ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      (α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F) →
      (α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F) →
      GsumC α k F Ψ ≤ C * Work.Spaces.HkSq α k F := by
  intro k hk
  obtain ⟨Cs, hCspos, hsrc⟩ := srcBoundFts D hD k hk
  obtain ⟨CA, hCApos, hA⟩ := Work.FTS.EllipticEst.remov.A_top_slot_bound D hD k hk
  refine ⟨Cs * (1 + CA ^ 2 + 2 * D ^ 2), by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk h1 h2
  have hTkA : α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ≤ CA ^ 2 * Work.Spaces.HkSq α k F := by
    have hAnn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Tk α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.FTS.EllipticEst.remov.Step.Tk_nonneg α k _
    have hA' := hA α F Ψ hα hα4 hwk h1 h2
    calc α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        = (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hAnn]; ring
      _ ≤ (CA * Work.Spaces.HkNorm α k F) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (sq_nonneg α) (Real.sqrt_nonneg _)) hA' 2
      _ = CA ^ 2 * Work.Spaces.HkSq α k F := by
          rw [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k F)]
  have hAcase : α ^ 4 * Work.Spaces.HkSq α (k - 1)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ≤ D ^ 2 * Work.Spaces.HkSq α k F := by
    have hb : 0 ≤ Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ) :=
      Work.Spaces.HkNorm_nonneg α (k - 1) _
    have h1' : α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ≤ D * Work.Spaces.HkNorm α k F := by
      linarith [h1]
    calc α ^ 4 * Work.Spaces.HkSq α (k - 1)
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        = (α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) ^ 2 := by
          rw [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α (k - 1) _)]
          ring
      _ ≤ (D * Work.Spaces.HkNorm α k F) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (sq_nonneg α)
            (Work.Spaces.HkNorm_nonneg α (k - 1) _)) h1' 2
      _ = D ^ 2 * Work.Spaces.HkSq α k F := by
          rw [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k F)]
  have hDzBcase : Work.Spaces.HkSq α (k - 1)
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) ≤ D ^ 2 * Work.Spaces.HkSq α k F := by
    have hb : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
      mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α (k - 1) _)
    have h2' : Work.Spaces.HkNorm α (k - 1)
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) ≤ D * Work.Spaces.HkNorm α k F := by
      linarith [h2]
    calc Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        = (Work.Spaces.HkNorm α (k - 1)
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))) ^ 2 := by
          rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α (k - 1) _)]
      _ ≤ (D * Work.Spaces.HkNorm α k F) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α (k - 1) _) h2' 2
      _ = D ^ 2 * Work.Spaces.HkSq α k F := by
          rw [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k F)]
  have hmain := hsrc α F Ψ hα hα4 hwk h1 h2
  calc GsumC α k F Ψ
      ≤ Cs * (Work.Spaces.HkSq α k F
          + α ^ 4 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
                z θ * Work.Spaces.Wt α z θ) ^ 2)
          + Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          + α ^ 4 * Work.Spaces.HkSq α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := hmain
    _ ≤ Cs * ((1 + CA ^ 2 + 2 * D ^ 2) * Work.Spaces.HkSq α k F) := by
        refine mul_le_mul_of_nonneg_left ?_ hCspos.le
        have hTkA' : α ^ 4 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed 0 k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              z θ * Work.Spaces.Wt α z θ) ^ 2) ≤ CA ^ 2 * Work.Spaces.HkSq α k F := hTkA
        linarith [hTkA', hAcase, hDzBcase]
    _ = (Cs * (1 + CA ^ 2 + 2 * D ^ 2)) * Work.Spaces.HkSq α k F := by ring

end Work.FTS.EllipticEst.Prop.BSlotTop
