import Mathlib
import Submission.Work.EKLC7.SmulMS
import Submission.Work.EKLC7.Defs

/-!
# `Work.EKLC7.restrict_smulSt` — pushing `μ.restrict Z` forward along `R_u`

For `μ` invariant under the subgroup `U ≤ SL₃(ℝ)` and `u ∈ U`, the restriction of `μ` to the
translate `smulSt u Z = R_u '' Z` of a set `Z` is the image under `R_u = (· ↦ u • ·)` of the
restriction of `μ` to `Z`.

The point is that `R_u` is a *homeomorphism* of `X₃` (the action is a continuous action of a
topological group, so `Homeomorph.smul u` applies), hence a measurable embedding, and that
`MeasurePreserving (R_u) μ μ` gives `μ.map R_u = μ`.  Putting the two together:
`(μ.map R_u).restrict (R_u '' Z) = (μ.restrict (R_u ⁻¹' R_u '' Z)).map R_u`
(`MeasurableEmbedding.restrict_map`), and `R_u ⁻¹' (R_u '' Z) = Z` by injectivity.
-/

namespace Work.EKLC7

open MeasureTheory
open Work.EKLContract

theorem restrict_smulSt {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {U : Subgroup Work.EKLContract.SL3} (hinv : Work.EKLContract.IsUInvariant μ U)
    {u : Work.EKLContract.SL3} (hu : u ∈ U) (Z : Set Work.EKLContract.X3) :
    μ.restrict (Work.EKLC7.smulSt u Z)
      = MeasureTheory.Measure.map (fun y : Work.EKLContract.X3 => u • y) (μ.restrict Z) := by
  have hEmb : MeasurableEmbedding (fun y : Work.EKLContract.X3 => u • y) :=
    (Homeomorph.smul u).toMeasurableEquiv.measurableEmbedding
  have hgen : (Measure.map (fun y : Work.EKLContract.X3 => u • y) μ).restrict
        ((fun y : Work.EKLContract.X3 => u • y) '' Z)
      = Measure.map (fun y : Work.EKLContract.X3 => u • y) (μ.restrict Z) := by
    rw [hEmb.restrict_map, Set.preimage_image_eq _ hEmb.injective]
  have hmap : Measure.map (fun y : Work.EKLContract.X3 => u • y) μ = μ := (hinv u hu).map_eq
  simpa [hmap] using hgen

end Work.EKLC7
