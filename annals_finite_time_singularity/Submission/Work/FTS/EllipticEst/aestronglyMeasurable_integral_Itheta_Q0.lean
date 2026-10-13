import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory
open scoped Real Topology

/-- **Measurability of the angular integral of a source on the open quadrant.**

If `g` is continuous on the open quadrant `Q0 = (0,∞) × (0,π/2)` and `φ` is continuous
on `Iθ = [0,π/2]`, then the angular integral
`z ↦ ∫_θ g z θ · φ θ dθ` is a.e. strongly measurable for the restricted Lebesgue
measure on `(0,∞)`.

Indeed the uncurried product is continuous on `Q0`, which is of full measure inside
`Iz × Iθ`, so the product function is a.e. strongly measurable for the product of the
restricted measures (`Work.Spaces.aesm_of_continuousOn_Qd`); integrating out the
`θ`-variable preserves a.e. strong measurability (Fubini for Bochner integrals,
`AEStronglyMeasurable.integral_prod_right'`). -/
theorem aestronglyMeasurable_integral_Itheta_Q0 (g : ℝ → ℝ → ℝ)
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ Work.Spaces.Iθ) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, g z θ * φ θ)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  -- The uncurried product is continuous on the open quadrant.
  have hgmul : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 * φ p.2) Q0 := by
    refine hg.mul ?_
    exact hφ.comp continuous_snd.continuousOn fun p hp => by
      obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
      exact ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  -- Hence it is a.e. strongly measurable for the product of the restricted measures.
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.1 p.2 * φ p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hgmul
  -- Integrating out `θ` preserves a.e. strong measurability.
  have h := MeasureTheory.AEStronglyMeasurable.integral_prod_right'
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) haesm
  -- `Iz = [0,∞)` agrees with `(0,∞)` up to the null set `{0}`.
  have hz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hz] at h
  simpa using h

end Work.FTS.EllipticEst
