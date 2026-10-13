import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsLimitDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

open MeasureTheory Set Filter
open scoped Real Topology

/-- **A.e. strong measurability of the `L₁₂`-density.**

`Work.FM.L12dens Work.Spaces.K Y s = ∫ θ in Iθ, K θ * Y s θ / s` is the angular
density of the fundamental model.  If the integrand `Y` is jointly a.e.-measurable
on `(0,∞) × Iθ` for the product of the restricted Lebesgue measures — the natural
hypothesis, since the full-plane pair `(s,θ) ↦ (K θ * Y s θ / s)` is *not* measurable
along `s = 0` — then the density is a.e.-strongly-measurable in `s`.

Proof: the multiplier `(s,θ) ↦ K θ / s` is (Borel) measurable on `ℝ × ℝ` (division is a
measurable operation on `ℝ`, with the junk value `0` at `s = 0`), so the product
`(s,θ) ↦ K θ / s * Y s θ` is a.e.-strongly-measurable for the product measure, hence so is
its `θ`-marginal by Fubini's measurability theorem
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`; the two expressions differ
only by the associativity of `*` / `⁻¹`, and `L12dens` is literally the set integral
against `volume.restrict Iθ`. -/
theorem aestronglyMeasurable_L12dens {Y : ℝ → ℝ → ℝ}
    (hY : AEMeasurable (Function.uncurry Y)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    MeasureTheory.AEStronglyMeasurable (fun s => Work.FM.L12dens Work.Spaces.K Y s)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hY' : MeasureTheory.AEStronglyMeasurable (Function.uncurry Y)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hY.aestronglyMeasurable
  have hK : Measurable (fun p : ℝ × ℝ => Work.Spaces.K p.2 / p.1) := by
    have h1 : Measurable fun θ : ℝ => Work.Spaces.K θ := by
      unfold Work.Spaces.K
      fun_prop
    exact (h1.comp measurable_snd).div measurable_fst
  have hprod : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 / p.1 * Y p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hK.aestronglyMeasurable.mul hY'
  have hprod' : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Y p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    convert hprod using 1
    funext p
    ring
  have h := hprod'.integral_prod_right'
  rw [show (fun s => Work.FM.L12dens Work.Spaces.K Y s)
      = fun s => ∫ θ, Work.Spaces.K θ * Y s θ / s
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) from by
    funext s
    rw [Work.FM.L12dens]
    rfl]
  exact h

end Work.FTS.StrongEps.E5Aux2
