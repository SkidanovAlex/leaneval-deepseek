import Mathlib

namespace Work.EKLC6Core

open MeasureTheory

theorem integral_sq_sub_const {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure ν] (h : X → ℝ) (c : ℝ)
    (h1 : MeasureTheory.Integrable h ν) (h2 : MeasureTheory.Integrable (fun y => h y ^ 2) ν) :
    ∫ y, (h y - c) ^ 2 ∂ν = ∫ y, h y ^ 2 ∂ν - 2 * c * ∫ y, h y ∂ν + c ^ 2 := by
  have hc : MeasureTheory.Integrable (fun _ : X => c ^ 2) ν := MeasureTheory.integrable_const _
  have hg : MeasureTheory.Integrable (fun y => 2 * c * h y) ν := h1.const_mul (2 * c)
  have hfg : MeasureTheory.Integrable (fun y => h y ^ 2 - 2 * c * h y) ν := h2.sub hg
  have hint : ∫ y, c ^ 2 ∂ν = c ^ 2 := by
    rw [MeasureTheory.integral_const]
    simp
  have hA : ∫ y, (h y - c) ^ 2 ∂ν = ∫ y, (h y ^ 2 - 2 * c * h y) ∂ν + ∫ y, c ^ 2 ∂ν := by
    rw [← MeasureTheory.integral_add hfg hc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    show (h y - c) ^ 2 = (h y ^ 2 - 2 * c * h y) + c ^ 2
    ring
  have hB : ∫ y, (h y ^ 2 - 2 * c * h y) ∂ν = ∫ y, h y ^ 2 ∂ν - ∫ y, 2 * c * h y ∂ν := by
    rw [MeasureTheory.integral_sub h2 hg]
  calc ∫ y, (h y - c) ^ 2 ∂ν
      = ∫ y, (h y ^ 2 - 2 * c * h y) ∂ν + ∫ y, c ^ 2 ∂ν := hA
    _ = (∫ y, h y ^ 2 ∂ν - ∫ y, 2 * c * h y ∂ν) + ∫ y, c ^ 2 ∂ν := by rw [hB]
    _ = (∫ y, h y ^ 2 ∂ν - (2 * c) * ∫ y, h y ∂ν) + c ^ 2 := by
          rw [MeasureTheory.integral_const_mul (2 * c) h, hint]
    _ = ∫ y, h y ^ 2 ∂ν - 2 * c * ∫ y, h y ∂ν + c ^ 2 := by ring

end Work.EKLC6Core
