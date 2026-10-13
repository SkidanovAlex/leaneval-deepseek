import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integrable_prod_of_lintegral_iterated
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3

open MeasureTheory Set Filter
open scoped Real Topology

/-- **Product-integrability of the `ℋ^k`-integrand, over the *half-open* product measure.**

`HkMem α k f` is stated with the closed intervals `Iz = [0,∞)` and `Iθ = [0,π/2]`: the
angular slices of `HkIntegrand α k f` are integrable on `Iθ` for every `z ∈ Iz`, and the
`z`-integral of those slices is integrable on `Iz`.  Since `f` is smooth on the open quadrant,
the uncurried integrand is continuous there, hence a.e. strongly measurable; Tonelli
(`Work.Spaces.integrable_prod_of_iterated`) then gives product-integrability for the product
of the two restricted measures. -/
theorem integrable_HkIntegrand_prod {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    MeasureTheory.Integrable (Function.uncurry (Work.Spaces.HkIntegrand α k f))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- a.e. strong measurability: the integrand is continuous on the open quadrant
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (Work.Spaces.HkIntegrand α k f))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    exact Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad α k
      (fun n => hsm.forall n)
  -- the angular slices are integrable for a.e. `z`, and the outer integral is integrable
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α k f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.ae_restrict_iff'
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    exact Filter.Eventually.of_forall fun z hz => hmem.1 z hz
  have houter : MeasureTheory.Integrable
      (fun z => ∫ θ, Work.Spaces.HkIntegrand α k f z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  exact (Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
    haesm hslice houter).1

theorem integrable_HkIntegrand {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    MeasureTheory.Integrable (Function.uncurry (Work.Spaces.HkIntegrand α k f))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := by
  have hint := integrable_HkIntegrand_prod hsm hmem
  -- `Quad = (0,∞) × (0,π/2)` agrees with `Iz ×ˢ Iθ` up to the coordinate hyperplanes and the
  -- two boundary lines `θ = 0`, `θ = π/2`, all of which are null for the planar Lebesgue measure.
  have hz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm
  have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := π / 2)).symm
  have hset : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  have hμ : MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad
      = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    change (MeasureTheory.volume.prod MeasureTheory.volume).restrict
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))
      = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    rw [← MeasureTheory.Measure.prod_restrict (Set.Ioi (0 : ℝ))
      (Set.Ioo (0 : ℝ) (π / 2))]
    rw [← MeasureTheory.Measure.restrict_congr_set hz,
      ← MeasureTheory.Measure.restrict_congr_set hθ]
  rw [hμ]
  exact hint

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3
