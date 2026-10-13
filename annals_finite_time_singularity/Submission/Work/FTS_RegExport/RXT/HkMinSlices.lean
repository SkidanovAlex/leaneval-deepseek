import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.C4.HkSqSwap_C4
import Submission.Work.FTS_RegExport.RXT.HkMinPrep
import Submission.Work.FTS_RegExport.RXT.slot_slice_data
import Submission.Work.FTS_RegExport.RXT.slot_slice_data_Wt
import Submission.Work.FTS.H2.LinfQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.HkMinSlices`

The `θ`-slice energies of the admissible slots of `HkIntegrand α 4`: for a datum which is `C⁴`
on the open quadrant and honestly in `ℋ⁴`, the slice energy `σ ↦ ∫_Iz (D_z^jD_θ^if · w)²` is
integrable, dominated slicewise by the `ℋ⁴`-integrand, and its `θ`-integral is at most
`HkSq α 4 f`.  The `Wt`-weighted version is provided for the mixed slots.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The two delegated helpers, repointed to their proved siblings -/

theorem tmp_slot_slice_data {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ)
    (hadm : (1 ≤ i ∧ i + j ≤ 4) ∨ (i = 0 ∧ j ≤ 4)) :
    AEMeasurable
        (fun σ => ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn
          (fun s => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz) ∧
      (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f :=
  slot_slice_data hα h4 hmem j i hadm

theorem tmp_slot_slice_data_Wt {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    AEMeasurable
        (fun σ => ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f :=
  slot_slice_data_Wt hα h4 hmem j i hi hij

/-! ## Slice energies of the admissible slots -/

/-- The `θ`-slice energy of an admissible slot: integrable, dominated slicewise by the
`ℋ⁴`-integrand, with `θ`-integral bounded by `HkSq`. -/
theorem slot_slice_all {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ) (hadm : FTSAdm j i) :
    MeasureTheory.Integrable
        (fun σ => ∫ x in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn
          (fun x => (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
          Work.Spaces.Iz) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
          ≤ (∫ x in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f x σ)) ∧
      (∫ σ in Work.Spaces.Iθ, ∫ x in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f := by
  obtain ⟨hae, hint, hbound⟩ := tmp_slot_slice_data (α := α) hα h4 hmem j i hadm
  obtain ⟨hNfin, hNint, hNae⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 h4 hmem
  have hcmp : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
        ≤ (∫ x in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f x σ) := by
    filter_upwards [hNae, Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hN hσ
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun x => by positivity) hN ?_
    exact Eventually.of_forall fun x => slot_pointwise_le hα j i hadm x hσ
  refine ⟨?_, hint, hcmp, hbound⟩
  refine MeasureTheory.Integrable.mono' hNint hae.aestronglyMeasurable ?_
  filter_upwards [hcmp] with σ hσ
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun x => by positivity)]
  exact hσ

/-- The same for the `Wt`-weighted mixed slots. -/
theorem slot_slice_Wt_all {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    MeasureTheory.Integrable
        (fun σ => ∫ x in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f x σ * Work.Spaces.Wt α x σ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed j i f x σ * Work.Spaces.Wt α x σ) ^ 2)
          ≤ (∫ x in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f x σ)) ∧
      (∫ σ in Work.Spaces.Iθ, ∫ x in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f x σ * Work.Spaces.Wt α x σ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f := by
  obtain ⟨hae, hbound⟩ := tmp_slot_slice_data_Wt (α := α) hα h4 hmem j i hi hij
  obtain ⟨hNfin, hNint, hNae⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 h4 hmem
  have hcmp : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed j i f x σ * Work.Spaces.Wt α x σ) ^ 2)
        ≤ (∫ x in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f x σ) := by
    filter_upwards [hNae] with σ hN
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun x => sq_nonneg _) hN ?_
    exact Eventually.of_forall fun x =>
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 f x σ i j hi hij
  refine ⟨?_, hcmp, hbound⟩
  refine MeasureTheory.Integrable.mono' hNint hae.aestronglyMeasurable ?_
  filter_upwards [hcmp] with σ hσ
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun x => sq_nonneg _)]
  exact hσ

end Work.FTS_RegExport.RXT
