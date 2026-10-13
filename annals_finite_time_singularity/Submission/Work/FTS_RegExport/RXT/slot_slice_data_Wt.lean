import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4
import Submission.Work.FTS_RegExport.C4.HkSqSwap_C4
import Submission.Work.FTS_RegExport.RXA1w.Helpers

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

/-- **The `θ`-slice data of one `W`-weighted mixed slot.**

For `f` of class `C⁴` on the open quadrant `Q0 = (0,∞) × (0,π/2)` which is honestly in `ℋ⁴`
(`Work.Spaces.HkMem α 4 f`), and for every mixed slot `D_z^j D_θ^i f` with `1 ≤ i` and
`i + j ≤ 4`, the angular function

  `σ ↦ ∫_s (D_z^jD_θ^if (s,σ) · W(s,σ))²`

is a.e. strongly measurable (in particular `AEMeasurable`), and its integral over `Iθ` is
bounded by `HkSq α 4 f`.

The argument is a single pointwise domination followed by two monotonicity steps:
the slot is one summand of `HkIntegrand α 4 f` (`Work.Spaces.sq_le_HkIntegrand_mixed`), so
`(D_z^jD_θ^if · W)² ≤ HkIntegrand α 4 f` pointwise; the `z`-slices of `HkIntegrand` are
integrable for a.e. `σ` and its `σ`-partial integral is integrable with total mass `HkSq α 4 f`
(`Work.FTS_RegExport.C4.HkSqSwap_C4`); monotonicity of the integral in each variable then
gives the bound.  Measurability of the `σ`-partial integral comes from the continuity of the
slot on the open quadrant (`Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn` and
`Work.FTS.StrongEps.continuousOn_Wt_Q0_fin`), which upgrades to a.e. strong measurability for
the product of the restricted measures (`Work.Spaces.aesm_of_continuousOn_Qd`), together with
`AEStronglyMeasurable.integral_prod_right'`. -/
theorem slot_slice_data_Wt {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    AEMeasurable
        (fun σ => ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f := by
  obtain ⟨hswap, hGint, hGslice⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 (α := α) h4 hmem
  -- ## Continuity of the uncurried weighted slot on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    ((Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn h4 hij).mul
      (Work.FTS.StrongEps.continuousOn_Wt_Q0_fin α)).pow 2
  have haesm1 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (by simpa only [Work.FTS.EllipticEst.Q0] using hcont)
  -- ## A.e. strong measurability of the `σ`-partial integral
  have haesm2 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.2 p.1 * Work.Spaces.Wt α p.2 p.1) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    haesm1.prod_swap
  have hΦsm : AEStronglyMeasurable (fun σ : ℝ => ∫ s in Work.Spaces.Iz,
      (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    haesm2.integral_prod_right'
  -- ## Pointwise domination by the `ℋ⁴`-integrand, a.e. in the angle
  have hbound : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
    filter_upwards [hGslice] with σ hσ
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun s => sq_nonneg _) hσ
      (Filter.Eventually.of_forall fun s =>
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s σ i j hi hij)
  -- ## Integrability of the `σ`-partial integral (needed for the a.e. bookkeeping)
  have hΦint : Integrable (fun σ : ℝ => ∫ s in Work.Spaces.Iz,
      (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine hGint.mono' hΦsm ?_
    filter_upwards [hbound] with σ hσ
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun s => sq_nonneg _)]
    exact hσ
  refine ⟨hΦsm.aemeasurable, ?_⟩
  calc (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
      ≤ ∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f s σ :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun σ =>
            MeasureTheory.integral_nonneg fun s => sq_nonneg _)
          hGint hbound
    _ = Work.Spaces.HkSq α 4 f := hswap

end Work.FTS_RegExport.RXT
