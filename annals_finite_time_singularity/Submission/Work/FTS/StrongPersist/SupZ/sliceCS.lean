import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory

namespace Work.FTS.StrongPersist.SupZ

/-- Slicewise Cauchy–Schwarz on the angular interval `Iθ = [0, π/2]`: for a fixed `s > 0`,
if the slices `θ ↦ Φ s θ` and `θ ↦ Φ' s θ` are (a.e.) strongly measurable on `Iθ` — which
follows from continuity of the corresponding two-variable functions on the open quadrant
`(0,∞) × (0,π/2)` — and square-integrable there, then

`∫_{Iθ} |Φ s θ · Φ' s θ| ≤ √( (∫_{Iθ} Φ s θ²) · (∫_{Iθ} Φ' s θ²) )`.

The proof converts the two `IntegrableOn` square hypotheses into `MemLp … 2` statements via
`memLp_two_iff_integrable_sq`, applies the abstract Cauchy–Schwarz inequality in `L²`
(`Work.Spaces.cs_integral`) to the absolute values, and takes square roots with
`Real.le_sqrt_of_sq_le`.  Note `open scoped Real` above is what makes the bare `π` in the
statement below denote `Real.pi` (matching `Work.Spaces.Iθ`); the statement itself is
otherwise unchanged. -/
theorem sliceCS {Φ Φ' : ℝ → ℝ → ℝ} {s : ℝ} (hs : 0 < s)
    (hcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hcont' : ContinuousOn (Function.uncurry Φ') (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hFin : MeasureTheory.IntegrableOn (fun θ : ℝ => Φ s θ ^ 2) Work.Spaces.Iθ)
    (hGin : MeasureTheory.IntegrableOn (fun θ : ℝ => Φ' s θ ^ 2) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, |Φ s θ * Φ' s θ|)
      ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, Φ s θ ^ 2) * (∫ θ in Work.Spaces.Iθ, Φ' s θ ^ 2)) := by
  -- the two slices are a.e. strongly measurable on `Iθ`
  have hΦm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Φ s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry Φ) hcont hs
  have hΨm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Φ' s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry Φ') hcont' hs
  -- hence the slices are in `L²(Iθ)`
  have hΦ : MeasureTheory.MemLp (fun θ : ℝ => Φ s θ) 2
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hΦm).2 hFin
  have hΨ : MeasureTheory.MemLp (fun θ : ℝ => Φ' s θ) 2
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hΨm).2 hGin
  -- Cauchy–Schwarz for the absolute values
  have hcs := Work.Spaces.cs_integral hΦ.abs hΨ.abs
  have hcs' : (∫ x in Work.Spaces.Iθ, |Φ s x| * |Φ' s x|) ^ 2
      ≤ (∫ x in Work.Spaces.Iθ, |Φ s x| ^ 2) * (∫ x in Work.Spaces.Iθ, |Φ' s x| ^ 2) := hcs
  -- `|Φ·Φ'| = |Φ|·|Φ'|` and `|Φ|² = Φ²`
  have hsq : (∫ θ in Work.Spaces.Iθ, |Φ s θ * Φ' s θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Φ s θ ^ 2) * (∫ θ in Work.Spaces.Iθ, Φ' s θ ^ 2) := by
    simpa only [abs_mul, sq_abs] using hcs'
  exact Real.le_sqrt_of_sq_le hsq

end Work.FTS.StrongPersist.SupZ
