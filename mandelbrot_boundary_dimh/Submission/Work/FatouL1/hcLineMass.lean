import Mathlib

namespace Work.FatouL1

/-- If every vertical line `y ↦ h (x + i y)` through `x ∈ (a,b)` is Bochner integrable and its
lintegral of the norm is bounded by `ofReal m`, then the ordinary Lebesgue integral of the norm
along that line is bounded by `max m 0`. -/
theorem hcLineMass {a b m : ℝ} {h : ℂ → ℂ}
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b, ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    ∫ y : ℝ, ‖h ((x : ℂ) + y * Complex.I)‖ ≤ max m 0 := by
  have hintx : MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)) := hint x hx
  have hfi : MeasureTheory.Integrable (fun y : ℝ => ‖h ((x : ℂ) + y * Complex.I)‖) := hintx.norm
  have hnn : 0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)]
      (fun y : ℝ => ‖h ((x : ℂ) + y * Complex.I)‖) :=
    Filter.Eventually.of_forall (fun y => norm_nonneg _)
  have heq := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi hnn
  have hle : ENNReal.ofReal (∫ y : ℝ, ‖h ((x : ℂ) + y * Complex.I)‖) ≤ ENNReal.ofReal m := by
    rw [heq]; exact hmass x hx
  have hfin := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hle
  rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at hfin
  have hI : 0 ≤ ∫ y : ℝ, ‖h ((x : ℂ) + y * Complex.I)‖ :=
    MeasureTheory.integral_nonneg (fun y => norm_nonneg _)
  rwa [max_eq_left hI] at hfin

end Work.FatouL1
