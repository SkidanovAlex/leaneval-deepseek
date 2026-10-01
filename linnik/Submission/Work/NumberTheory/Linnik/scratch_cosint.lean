import Mathlib

open MeasureTheory intervalIntegral
open scoped Real

set_option autoImplicit false

namespace Commons.NumberTheory.Linnik

/-- For a non-negative continuous `g` on `[0,x₀]`, `∫₀^{x₀} g(t)·cos(c t) ≤ ∫₀^{x₀} g(t)`.
This is the elementary inequality behind Heath-Brown §6 (the step
`ℜF(-λ'+iμ') - ℜF(λ₁-λ'+iμ') ≤ F(-λ') - F(λ₁-λ')` in the passage from (6.18) to Lemma 6.3). -/
theorem integral_mul_cos_le {x₀ c : ℝ} (hx₀ : 0 < x₀) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc 0 x₀)) (hgnn : ∀ t ∈ Set.Icc (0:ℝ) x₀, 0 ≤ g t) :
    (∫ t in (0:ℝ)..x₀, g t * Real.cos (c * t)) ≤ ∫ t in (0:ℝ)..x₀, g t := by
  have hui : Set.uIcc (0:ℝ) x₀ = Set.Icc 0 x₀ := Set.uIcc_of_le hx₀.le
  have hcoscont : Continuous (fun t : ℝ => Real.cos (c * t)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hcont1 : ContinuousOn (fun t : ℝ => g t * Real.cos (c * t)) (Set.uIcc (0:ℝ) x₀) := by
    rw [hui]; exact hg.mul hcoscont.continuousOn
  have hcont2 : ContinuousOn (fun t : ℝ => g t) (Set.uIcc (0:ℝ) x₀) := by rw [hui]; exact hg
  refine intervalIntegral.integral_mono_on hx₀.le hcont1.intervalIntegrable
    hcont2.intervalIntegrable ?_
  intro t ht
  have hc : Real.cos (c * t) ≤ 1 := Real.cos_le_one _
  have hg0 : 0 ≤ g t := hgnn t ht
  nlinarith [mul_le_mul_of_nonneg_left hc hg0]

/-- Difference form: for `0 ≤ g₂ ≤ g₁` on `[0,x₀]`,
`∫ (g₁-g₂)cos ≤ ∫ (g₁-g₂)`; used for
`ℜF(-λ'+iμ') - ℜF(λ₁-λ'+iμ') ≤ F(-λ') - F(λ₁-λ')`. -/
theorem integral_cos_sub_le {x₀ c : ℝ} (hx₀ : 0 < x₀) {g₁ g₂ : ℝ → ℝ}
    (hg₁ : ContinuousOn g₁ (Set.Icc 0 x₀)) (hg₂ : ContinuousOn g₂ (Set.Icc 0 x₀))
    (hg₁nn : ∀ t ∈ Set.Icc (0:ℝ) x₀, 0 ≤ g₁ t) (hg₂nn : ∀ t ∈ Set.Icc (0:ℝ) x₀, 0 ≤ g₂ t)
    (hle : ∀ t ∈ Set.Icc (0:ℝ) x₀, g₂ t ≤ g₁ t) :
    (∫ t in (0:ℝ)..x₀, g₁ t * Real.cos (c * t)) - (∫ t in (0:ℝ)..x₀, g₂ t * Real.cos (c * t))
      ≤ (∫ t in (0:ℝ)..x₀, g₁ t) - (∫ t in (0:ℝ)..x₀, g₂ t) := by
  have hui : Set.uIcc (0:ℝ) x₀ = Set.Icc 0 x₀ := Set.uIcc_of_le hx₀.le
  have hcoscont : Continuous (fun t : ℝ => Real.cos (c * t)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hcos : ∀ t, Real.cos (c * t) ≤ 1 := fun t => Real.cos_le_one _
  have hu1 : ContinuousOn (fun t : ℝ => g₁ t * Real.cos (c * t)) (Set.uIcc (0:ℝ) x₀) := by
    rw [hui]; exact hg₁.mul hcoscont.continuousOn
  have hu2 : ContinuousOn (fun t : ℝ => g₂ t * Real.cos (c * t)) (Set.uIcc (0:ℝ) x₀) := by
    rw [hui]; exact hg₂.mul hcoscont.continuousOn
  have hu3 : ContinuousOn (fun t : ℝ => g₁ t) (Set.uIcc (0:ℝ) x₀) := by rw [hui]; exact hg₁
  have hu4 : ContinuousOn (fun t : ℝ => g₂ t) (Set.uIcc (0:ℝ) x₀) := by rw [hui]; exact hg₂
  have hudd : ContinuousOn (fun t : ℝ => g₁ t - g₂ t) (Set.uIcc (0:ℝ) x₀) := hu3.sub hu4
  have huc : ContinuousOn (fun t : ℝ => (g₁ t - g₂ t) * Real.cos (c * t)) (Set.uIcc (0:ℝ) x₀) :=
    hudd.mul hcoscont.continuousOn
  have hmono : (∫ t in (0:ℝ)..x₀, (g₁ t - g₂ t) * Real.cos (c * t))
      ≤ ∫ t in (0:ℝ)..x₀, (g₁ t - g₂ t) := by
    refine intervalIntegral.integral_mono_on hx₀.le huc.intervalIntegrable
      hudd.intervalIntegrable ?_
    intro t ht
    have hc : Real.cos (c * t) ≤ 1 := hcos t
    have h0 : 0 ≤ g₁ t - g₂ t := by linarith [hle t ht]
    nlinarith [mul_le_mul_of_nonneg_left hc h0]
  have hcong1 : (∫ t in (0:ℝ)..x₀, (g₁ t - g₂ t) * Real.cos (c * t))
      = ∫ t in (0:ℝ)..x₀, (g₁ t * Real.cos (c * t) - g₂ t * Real.cos (c * t)) := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hcong1, intervalIntegral.integral_sub hu1.intervalIntegrable hu2.intervalIntegrable,
    intervalIntegral.integral_sub hu3.intervalIntegrable hu4.intervalIntegrable] at hmono
  exact hmono

end Commons.NumberTheory.Linnik
