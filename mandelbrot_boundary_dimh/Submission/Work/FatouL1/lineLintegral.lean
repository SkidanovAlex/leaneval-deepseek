import Mathlib

namespace Work.FatouL1

open MeasureTheory

/-- The integral of `‖u y‖` over the segment `[-Y, Y]` is bounded by the whole-line
`lintegral` of `ENNReal.ofReal ‖u y‖`. -/
theorem lineLintegral {u : ℝ → ℂ} (hu : Continuous u) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∫⁻ y : ℝ, ENNReal.ofReal ‖u y‖ ≤ ENNReal.ofReal ε) {Y : ℝ} (hY : 0 ≤ Y) :
    ∫ y : ℝ in (-Y)..Y, ‖u y‖ ≤ ε := by
  have hle : -Y ≤ Y := by linarith
  have hmeas : AEStronglyMeasurable (fun y : ℝ => ‖u y‖) (volume.restrict (Set.Ioc (-Y) Y)) :=
    (hu.norm.measurable.aestronglyMeasurable).restrict
  have hnn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioc (-Y) Y)] (fun y : ℝ => ‖u y‖) :=
    Filter.Eventually.of_forall (fun y => norm_nonneg _)
  have hstep : ENNReal.ofReal (∫ y : ℝ in (-Y)..Y, ‖u y‖) ≤
      ∫⁻ y : ℝ, ENNReal.ofReal ‖u y‖ := by
    rw [intervalIntegral.integral_of_le hle]
    calc ENNReal.ofReal (∫ y : ℝ in Set.Ioc (-Y) Y, ‖u y‖)
        = ENNReal.ofReal ((∫⁻ y : ℝ in Set.Ioc (-Y) Y, ENNReal.ofReal ‖u y‖).toReal) := by
          rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
      _ ≤ ∫⁻ y : ℝ in Set.Ioc (-Y) Y, ENNReal.ofReal ‖u y‖ := ENNReal.ofReal_toReal_le
      _ ≤ ∫⁻ y : ℝ, ENNReal.ofReal ‖u y‖ := by
          simpa using lintegral_mono_set (μ := volume) (f := fun y : ℝ => ENNReal.ofReal ‖u y‖)
            (s := Set.Ioc (-Y) Y) (t := Set.univ) (Set.subset_univ _)
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp (hstep.trans h)

end Work.FatouL1
