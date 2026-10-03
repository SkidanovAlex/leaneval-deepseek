import Mathlib

namespace Work.FatouL1

open MeasureTheory Set

/-- For a real function `f` which is almost everywhere nonnegative, the `ENNReal.ofReal` of the
Bochner integral is bounded by the `lintegral` of `ENNReal.ofReal f`: if `f` is integrable this is
an equality, and otherwise the Bochner integral is `0` by convention while the `lintegral` is
nonnegative. -/
theorem ofReal_integral_le_lintegral_ofReal {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ} (h0 : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · exact le_of_eq (ofReal_integral_eq_lintegral_ofReal h h0)
  · rw [integral_undef h, ENNReal.ofReal_zero]; positivity

/-- Jensen + Tonelli: the `y`-integral of the `ofReal` of the interval primitive of `h` is
bounded by the double `lintegral` of `ofReal (h y s)` over `y ∈ ℝ`, `s ∈ [0,1]`. -/
theorem lintegralPrimitiveLeMass {h : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry h) ((Set.univ : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1))
    (hnonneg : ∀ y s, 0 ≤ h y s) :
    ∫⁻ y : ℝ, ENNReal.ofReal (∫ s in (0:ℝ)..1, h y s)
      ≤ ∫⁻ s in Set.Icc (0:ℝ) 1, ∫⁻ y : ℝ, ENNReal.ofReal (h y s) := by
  -- Pointwise step: `ofReal (∫_0^1 h y s ds) ≤ ∫⁻ s ∈ [0,1], ofReal (h y s)`.
  have hpt : ∀ y : ℝ, ENNReal.ofReal (∫ s in (0:ℝ)..1, h y s)
      ≤ ∫⁻ s in Set.Icc (0:ℝ) 1, ENNReal.ofReal (h y s) := by
    intro y
    have hle := ofReal_integral_le_lintegral_ofReal
      (μ := volume.restrict (Set.Icc (0:ℝ) 1)) (f := fun s => h y s)
      (Filter.Eventually.of_forall (fun s => hnonneg y s))
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine le_trans (le_of_eq ?_) hle
    exact congrArg ENNReal.ofReal (setIntegral_congr_set Ioc_ae_eq_Icc)
  calc ∫⁻ y : ℝ, ENNReal.ofReal (∫ s in (0:ℝ)..1, h y s)
      ≤ ∫⁻ y : ℝ, ∫⁻ s in Set.Icc (0:ℝ) 1, ENNReal.ofReal (h y s) := lintegral_mono hpt
    _ = ∫⁻ s in Set.Icc (0:ℝ) 1, ∫⁻ y : ℝ, ENNReal.ofReal (h y s) := by
        -- Tonelli: swap the two integrals (measurability of `ofReal (h y s)` on the product).
        have hK : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) :=
          MeasurableSet.univ.prod measurableSet_Icc
        have hcontG : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal (Function.uncurry h p))
            ((Set.univ : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) :=
          ENNReal.continuous_ofReal.comp_continuousOn hcont
        have hae : AEMeasurable (Function.uncurry fun y s => ENNReal.ofReal (h y s))
            (volume.prod (volume.restrict (Set.Icc (0:ℝ) 1))) := by
          have h := hcontG.aemeasurable (μ := volume.prod volume) hK
          rwa [← Measure.prod_restrict, Measure.restrict_univ] at h
        exact lintegral_lintegral_swap hae

end Work.FatouL1
