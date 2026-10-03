import Mathlib
import Submission.Work.FatouL1.lintegralPrimitiveLeMass

namespace Work.FatouL1

open MeasureTheory Set

/-- Tonelli/Jensen for a general interval `[a,b]`: the `y`-lintegral of the `ofReal` of the
interval integral of `h y` over `[a,b]` is bounded by the double `lintegral` of `ofReal (h y s)`
over `s ∈ [a,b]` and `y : ℝ`.

This is the general-interval version of `lintegralPrimitiveLeMass`. -/
theorem lintegral_interval_le {h : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn (Function.uncurry h) ((Set.univ : Set ℝ) ×ˢ Set.Icc a b))
    (hnonneg : ∀ y s, 0 ≤ h y s) :
    ∫⁻ y : ℝ, ENNReal.ofReal (∫ s in a..b, h y s) ≤
      ∫⁻ s in Set.Icc a b, ∫⁻ y : ℝ, ENNReal.ofReal (h y s) := by
  -- Pointwise step: `ofReal (∫_a^b h y s ds) ≤ ∫⁻ s ∈ [a,b], ofReal (h y s)`.
  have hpt : ∀ y : ℝ, ENNReal.ofReal (∫ s in a..b, h y s)
      ≤ ∫⁻ s in Set.Icc a b, ENNReal.ofReal (h y s) := by
    intro y
    have hle := ofReal_integral_le_lintegral_ofReal
      (μ := volume.restrict (Set.Icc a b)) (f := fun s => h y s)
      (Filter.Eventually.of_forall (fun s => hnonneg y s))
    rw [intervalIntegral.integral_of_le hab]
    refine le_trans (le_of_eq ?_) hle
    exact congrArg ENNReal.ofReal (setIntegral_congr_set Ioc_ae_eq_Icc)
  calc ∫⁻ y : ℝ, ENNReal.ofReal (∫ s in a..b, h y s)
      ≤ ∫⁻ y : ℝ, ∫⁻ s in Set.Icc a b, ENNReal.ofReal (h y s) := lintegral_mono hpt
    _ = ∫⁻ s in Set.Icc a b, ∫⁻ y : ℝ, ENNReal.ofReal (h y s) := by
        -- Tonelli: swap the two integrals (measurability of `ofReal (h y s)` on the product).
        have hK : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Set.Icc a b) :=
          MeasurableSet.univ.prod measurableSet_Icc
        have hcontG : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal (Function.uncurry h p))
            ((Set.univ : Set ℝ) ×ˢ Set.Icc a b) :=
          ENNReal.continuous_ofReal.comp_continuousOn hcont
        have hae : AEMeasurable (Function.uncurry fun y s => ENNReal.ofReal (h y s))
            (volume.prod (volume.restrict (Set.Icc a b))) := by
          have h := hcontG.aemeasurable (μ := volume.prod volume) hK
          rwa [← Measure.prod_restrict, Measure.restrict_univ] at h
        exact lintegral_lintegral_swap hae

end Work.FatouL1
