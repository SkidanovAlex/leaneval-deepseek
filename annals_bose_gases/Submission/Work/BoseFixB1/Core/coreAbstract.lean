import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseFixB1.Core

/-- Fubini slice integrability in the first variable: the first marginal of an integrable
function on the product is integrable. -/
theorem coreFubini_left {E : Type*} [MeasurableSpace E] {μ : MeasureTheory.Measure E}
    [MeasureTheory.SFinite μ] (K : E → E → ℂ) (v : E → ℂ)
    (hvK : MeasureTheory.Integrable (Function.uncurry (fun y z => v z * K y z)) (μ.prod μ)) :
    MeasureTheory.Integrable (fun y => ∫ z, v z * K y z ∂μ) μ := by
  simpa [Function.uncurry] using hvK.integral_prod_left

theorem coreAbstract {E : Type*} [MeasurableSpace E] {μ : MeasureTheory.Measure E}
    [MeasureTheory.SFinite μ]
    (K : E → E → ℂ) (u v : E → ℂ) (C₁ C₂ : ℂ)
    (hsliceK : ∀ y, MeasureTheory.Integrable (K y) μ)
    (hsliceVK : ∀ y, MeasureTheory.Integrable (fun z => v z * K y z) μ)
    (hvK : MeasureTheory.Integrable (Function.uncurry (fun y z => v z * K y z)) (μ.prod μ))
    (huvK : MeasureTheory.Integrable (Function.uncurry (fun y z => u y * (v z * K y z)))
      (μ.prod μ))
    (hmz : ∀ y, ∫ z, K y z ∂μ = 0) (hmy : ∀ z, ∫ y, K y z ∂μ = 0) :
    (∫ y, ∫ z, (u y - C₁) * (v z - C₂) * K y z ∂μ ∂μ)
      = (∫ y, ∫ z, u y * v z * K y z ∂μ ∂μ) := by
  have hAint : Integrable (fun y => ∫ z, v z * K y z ∂μ) μ :=
    coreFubini_left K v hvK
  have hUAint : Integrable (fun y => u y * ∫ z, v z * K y z ∂μ) μ := by
    have h1 : Integrable (fun y => ∫ z, u y * (v z * K y z) ∂μ) μ := by
      simpa [Function.uncurry] using huvK.integral_prod_left
    have h2 : (fun y => ∫ z, u y * (v z * K y z) ∂μ) = fun y => u y * ∫ z, v z * K y z ∂μ := by
      funext y
      rw [integral_const_mul]
    rw [h2] at h1
    exact h1
  have hAzero : ∫ y, (∫ z, v z * K y z ∂μ) ∂μ = 0 := by
    rw [integral_integral_swap hvK]
    have hthis : ∀ z, ∫ y, v z * K y z ∂μ = v z * 0 := by
      intro z
      rw [integral_const_mul, hmy z]
    simp only [hthis]
    simp
  calc ∫ y, ∫ z, (u y - C₁) * (v z - C₂) * K y z ∂μ ∂μ
      = ∫ y, (u y - C₁) * (∫ z, v z * K y z ∂μ) ∂μ := by
        apply integral_congr_ae
        filter_upwards with y
        have hs : ∫ z, (v z - C₂) * K y z ∂μ = ∫ z, v z * K y z ∂μ - C₂ * ∫ z, K y z ∂μ := by
          have h1 : ∫ z, (v z - C₂) * K y z ∂μ = ∫ z, v z * K y z - C₂ * K y z ∂μ := by
            apply integral_congr_ae
            filter_upwards with z
            ring
          rw [h1, integral_sub (hsliceVK y) ((hsliceK y).const_mul C₂), integral_const_mul]
        have h2 : ∫ z, (u y - C₁) * (v z - C₂) * K y z ∂μ
            = (u y - C₁) * ∫ z, (v z - C₂) * K y z ∂μ := by
          rw [← integral_const_mul (u y - C₁) (fun z => (v z - C₂) * K y z)]
          apply integral_congr_ae
          filter_upwards with z
          ring
        rw [h2, hs, hmz y, mul_zero, sub_zero]
    _ = ∫ y, (u y * (∫ z, v z * K y z ∂μ) - C₁ * (∫ z, v z * K y z ∂μ)) ∂μ := by
        apply integral_congr_ae
        filter_upwards with y
        ring
    _ = ∫ y, u y * (∫ z, v z * K y z ∂μ) ∂μ
          - ∫ y, C₁ * (∫ z, v z * K y z ∂μ) ∂μ :=
        integral_sub hUAint (hAint.const_mul C₁)
    _ = ∫ y, u y * (∫ z, v z * K y z ∂μ) ∂μ
          - C₁ * ∫ y, (∫ z, v z * K y z ∂μ) ∂μ := by
        rw [integral_const_mul]
    _ = ∫ y, u y * (∫ z, v z * K y z ∂μ) ∂μ := by
        rw [hAzero, mul_zero, sub_zero]
    _ = ∫ y, ∫ z, u y * v z * K y z ∂μ ∂μ := by
        symm
        apply integral_congr_ae
        filter_upwards with y
        have h3 : ∫ z, u y * v z * K y z ∂μ = u y * ∫ z, v z * K y z ∂μ := by
          have h : ∫ z, u y * v z * K y z ∂μ = ∫ z, u y * (v z * K y z) ∂μ := by
            apply integral_congr_ae
            filter_upwards with z
            ring
          rw [h, integral_const_mul]
        exact h3

end Work.BoseFixB1.Core
