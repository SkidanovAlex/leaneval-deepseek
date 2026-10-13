/-
# `ModalSolR/SourcePrep` — slice measurability/integrability for the source-side limit

Auxiliary facts about the angular slices of a source `F : ℝ → ℝ → ℝ` which is `C^∞` on the open
quadrant `Q0 = (0,∞) × (0,π/2)` and whose square is integrable there:

* `sigma_integrable` — the angular slice energy `z ↦ ∫_θ F z θ ^ 2 cos θ` is integrable in `z`;
* `ae_slice_facts` — for almost every `z > 0` the slice `θ ↦ F z θ` is a.e. strongly measurable
  and its square is integrable against `cos θ` on `Iθ`.

Both are used by `Work.FTS.H2.ModalSolR.sourceSideLimit`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.FTS.EllipticEst.LevelOneAsm.ParsevalZIntAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

/-- The slice energy `z ↦ ∫_θ F z θ ^ 2 cos θ` of an `L²` source is integrable in `z` (its
integral is the double integral of `F ^ 2 cos θ` over the quadrant, which is finite). -/
theorem sigma_integrable {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hL2' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    show MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    rw [Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
    exact hL2
  have hprod : (((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)).prod
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ))
      = (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  have hF2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
    rw [hprod]; exact hL2'
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2)
      (((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
    have h1 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
        (((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)).prod
          ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
      rw [hprod, Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
      exact hsm.continuousOn.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    exact (h1.pow 2).mul (Real.continuous_cos.comp continuous_snd).aestronglyMeasurable
  have hbound : ∀ᵐ p ∂(((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ)),
      ‖F p.1 p.2 ^ 2 * Real.cos p.2‖ ≤ F p.1 p.2 ^ 2 := by
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc F p.1 p.2 ^ 2 * |Real.cos p.2| ≤ F p.1 p.2 ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one p.2) (sq_nonneg _)
      _ = F p.1 p.2 ^ 2 := by ring
  have hF2cos : MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2)
      (((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ)) :=
    MeasureTheory.Integrable.mono' hF2 hmeas hbound
  simpa only using hF2cos.integral_prod_left

/-- For almost every `z > 0` the angular slice `θ ↦ F z θ` of an `L²` source is a.e. strongly
measurable and its square is integrable against `cos θ` on `Iθ`. -/
theorem ae_slice_facts {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.AEStronglyMeasurable (fun θ => F z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ := by
  have h1 : MeasureTheory.AEStronglyMeasurable (Function.uncurry F)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) := by
    rw [Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
    exact hsm.continuousOn.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  have hL2' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    show MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    rw [Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
    exact hL2
  have h2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hL2' ?_ ?_
    · exact ((h1.pow 2).mul (Real.continuous_cos.comp continuous_snd).aestronglyMeasurable)
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc F p.1 p.2 ^ 2 * |Real.cos p.2| ≤ F p.1 p.2 ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one p.2) (sq_nonneg _)
        _ = F p.1 p.2 ^ 2 := by ring
  exact (Work.FTS.EllipticEst.LevelOneAsm.sliceSM_of_hyp h1).and
    (Work.FTS.EllipticEst.LevelOneAsm.sliceSqInt_of_hyp h2)

end Work.FTS.H2.ModalSolR
