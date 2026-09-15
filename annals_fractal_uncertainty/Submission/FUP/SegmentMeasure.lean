import ChallengeDeps
import Submission.FUP.LineRestriction
import Submission.Commons.Measure.Real.porous_interval_measure_bound

open FractalUncertainty
open MeasureTheory FourierTransform Metric
open scoped ENNReal

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-- Corollary of Cohen's paper (Appendix, `cor:line_porous_small_intersection`): a
`ν`-porous-on-lines set intersects every unit-speed segment of length `R ∈ (α₀, α₁)` in a set
of one-dimensional measure `≤ C·R·(α₀/R)^γ`.

The one-dimensional measure of the intersection is understood through the isometric
parametrisation `t ↦ p + t·v` of the segment, i.e. as the Lebesgue measure of the pulled-back
set `(t : ℝ) ↦ p + t·v` applied to `Y ∩ γ([0,R])`. -/
lemma line_porous_segment_measure {ν α₀ α₁ : ℝ} {Y : Set ℝᵈ} (hν : 0 < ν) (hα₀ : 0 < α₀)
    (hYm : MeasurableSet Y) (hY : PorousOnLines ν α₀ α₁ Y)
    (p v : ℝᵈ) (hv : ‖v‖ = 1) {R : ℝ} (hR : R ∈ Set.Ioo α₀ α₁) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      (MeasureTheory.volume ((fun t : ℝ => p + t • v) ⁻¹' Y ∩ Set.Icc 0 R) : ENNReal) ≤
        ENNReal.ofReal (C * R * (α₀ / R) ^ γ) := by
  let Z : Set ℝ := (fun t : ℝ => p + t • v) ⁻¹' Y
  have hZpor : PorousIntervals ν α₀ α₁ Z := pullback_porous_of_unitSpeed p v hv hα₀ hY
  have hγcont : Continuous (fun t : ℝ => p + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hZmeas : MeasurableSet Z := by
    simpa [Z] using hYm.preimage hγcont.measurable
  rcases Commons.Measure.Real.porous_interval_measure_bound (ν := ν) (α₀ := α₀) (α₁ := α₁)
      hν hα₀ hZmeas
      (by
        intro y R' hR'
        rcases hZpor y R' hR' with ⟨x, hx, hmem⟩
        exact ⟨x, hx, hmem⟩)
      (a := 0) (b := R) (by simpa using hR)
    with ⟨γ, C, hγ, hC, hbd⟩
  refine ⟨γ, C, hγ, hC, ?_⟩
  have hR0 : R - 0 = R := by ring
  have harg : C * (R - 0) * ((α₀ / (R - 0)) ^ γ) = C * R * (α₀ / R) ^ γ := by
    rw [hR0]
  calc
    volume ((fun t : ℝ => p + t • v) ⁻¹' Y ∩ Set.Icc 0 R) = volume (Z ∩ Set.Icc 0 R) := by rfl
    _ ≤ ENNReal.ofReal (C * (R - 0) * ((α₀ / (R - 0)) ^ γ)) := hbd
    _ = ENNReal.ofReal (C * R * (α₀ / R) ^ γ) := by rw [harg]

end Submission.FUP
