import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.MixedMulDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.Spaces

/-- For `z > 0`, the slice `θ ↦ g (z, θ)` is continuous on the open interval `(0, π/2)`,
hence almost everywhere strongly measurable for the measure `volume.restrict Iθ`
(the two endpoints `0` and `π/2` form a null set). -/
theorem aesm_slice_of_continuousOn_Qd (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable (fun θ => g (z, θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  -- the slice map `θ ↦ (z, θ)` maps `(0, π/2)` into the open quadrant
  have hcont : ContinuousOn (fun θ : ℝ => g (z, θ)) (Set.Ioo 0 (π / 2)) :=
    hg.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => ⟨hz, hθ⟩)
  -- continuity on the open interval gives a.e. strong measurability there
  have h1 : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => g (z, θ))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  -- `(0, π/2)` and `Iθ = [0, π/2]` differ by the two null endpoints
  have hset : (Set.Ioo (0 : ℝ) (π / 2)) =ᵐ[MeasureTheory.volume]
      (Set.Icc (0 : ℝ) (π / 2)) :=
    MeasureTheory.Ioo_ae_eq_Icc
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    (MeasureTheory.Measure.restrict_congr_set hset).symm
  rw [hmeas]
  exact h1

end Work.Spaces
