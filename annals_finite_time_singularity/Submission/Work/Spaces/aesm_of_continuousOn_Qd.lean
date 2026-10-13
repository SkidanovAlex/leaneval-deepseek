import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.MixedMulDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.Spaces

/-- If `g` is continuous on the open quadrant `(0,∞) × (0,π/2)`, then it is almost everywhere
strongly measurable with respect to the product of the restrictions of Lebesgue measure to
`Iz = [0,∞)` and `Iθ = [0,π/2]`.  Indeed that product measure is the restriction of the planar
Lebesgue measure to `Iz ×ˢ Iθ`, which equals the open quadrant up to a null set (the difference
being contained in the coordinate hyperplanes and the two boundary lines `θ = 0`, `θ = π/2`). -/
theorem aesm_of_continuousOn_Qd (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable g
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- `Iz` agrees a.e. with the open half-line and `Iθ` a.e. with the open interval.
  have hz : Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : (Iz ×ˢ Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume]
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  -- The open quadrant is measurable, so continuity there gives almost everywhere strong
  -- measurability for the restricted planar Lebesgue measure.
  have hUm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable g
      ((volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :=
    hg.aestronglyMeasurable hUm
  rw [MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact hmain

end Work.Spaces
