import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open MeasureTheory Set

/-- **A.e. measurability of the `z`-slice integral of a function continuous on the open
quadrant.**  If `G : ℝ × ℝ → ℝ` is continuous on the open quadrant `(0,∞) × (0,π/2)`, then the
partial integral `θ ↦ ∫⁻_z ofReal (G z θ)` over `z ∈ (0,∞)` is a.e. measurable w.r.t. the
Lebesgue measure restricted to `(0,π/2)`.  No behaviour of `G` outside the open quadrant is
assumed (it is irrelevant, since both restricted measures are concentrated there).

This is the Fubini/Tonelli measurability input needed to apply
`Work.FTS.EllipticEst.Blocks.lintegral_mul_add_le` in `TermAgmon`: the functions whose
measurability is needed there are exactly `θ ↦ ∫⁻_z ofReal ((z² ∂_z²V (z,θ) · w z)²)` and
`θ ↦ ∫⁻_z ofReal ((V (z,θ) · w z)²)`, with `V ∈ SmoothOpen` (so that
`Work.Spaces.pzIter 2 V` and `V` are continuous on the open quadrant) and `w` the radial weight.

ROUTE.  The joint integrand `fun p : ℝ × ℝ => ENNReal.ofReal (G p)` is
`ContinuousOn _ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2))` (compose `hG` with the continuous
`ENNReal.continuous_ofReal`), the product set is open hence measurable, so
`ContinuousOn.aemeasurable` gives `AEMeasurable` of the joint integrand for the measure
`(volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2))` (note
`(volume : Measure (ℝ × ℝ)) = volume.prod volume`).  Rewrite this measure as
`(volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π/2)))` by
`Measure.prod_restrict`, then apply `AEMeasurable.lintegral_prod_left'` (with the `z`-variable
as the first coordinate and `β = ℝ` the `θ`-variable).  There is a precedent for exactly this
argument in the workspace (`_rev_aemeas_linTheta.lean`). -/
theorem aemeasurable_lintegral_of_continuousOn_Qd {G : ℝ × ℝ → ℝ}
    (hG : ContinuousOn G (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEMeasurable
      (fun θ => MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal (G (z, θ))))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
  -- The quadrant is a product of measurable sets.
  have hQm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  -- The joint integrand is continuous on the quadrant: compose `hG` with `ENNReal.ofReal`.
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal (G p))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ENNReal.continuous_ofReal.comp_continuousOn hG
  -- Hence it is a.e. strongly measurable for the product of the two restricted measures.
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (G p))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))) := by
    rw [Measure.prod_restrict]
    exact hcont.aestronglyMeasurable hQm
  -- Fubini/Tonelli for `∫⁻` gives a.e. measurability of the slice integral in the second variable.
  exact haesm.aemeasurable.lintegral_prod_left'

end Work.FTS.EllipticEst.Blocks
