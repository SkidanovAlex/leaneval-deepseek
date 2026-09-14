import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section

open Real MeasureTheory Set
open scoped Real

namespace Commons.Analysis.GaussianMeasure

/-- Gaussian tail shift inequality: for `σ, ρ ≥ 0`,
`∫_{x > σ+ρ} exp (-π x²) ≤ exp (-π ρ²) · ∫_{x > σ} exp (-π x²)`.

Proof idea: substitute `x = u + ρ` in the left integral (translation invariance of
Lebesgue measure), then use the pointwise bound
`exp (-π (u+ρ)²) ≤ exp (-π ρ²) · exp (-π u²)` valid for `u ≥ 0`. -/
theorem tail_shift_le (σ ρ : ℝ) (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ) :
    (∫ x in Set.Ioi (σ + ρ), Real.exp (-Real.pi * x ^ 2)) ≤
      Real.exp (-Real.pi * ρ ^ 2) * (∫ x in Set.Ioi σ, Real.exp (-Real.pi * x ^ 2)) := by
  -- (1) change of variables x ↦ u + ρ
  have hsubst :
      (∫ x in Set.Ioi (σ + ρ), Real.exp (-Real.pi * x ^ 2)) =
        ∫ u in Set.Ioi σ, Real.exp (-Real.pi * (u + ρ) ^ 2) := by
    have hmap : Measure.map (fun u : ℝ => u + ρ) (volume : Measure ℝ) = volume := by
      exact MeasureTheory.map_add_right_eq_self volume ρ
    calc
      (∫ x in Set.Ioi (σ + ρ), Real.exp (-Real.pi * x ^ 2) ∂(volume : Measure ℝ))
          = ∫ x in Set.Ioi (σ + ρ), Real.exp (-Real.pi * x ^ 2)
              ∂(Measure.map (fun u : ℝ => u + ρ) volume) := by
              rw [hmap]
      _ = ∫ u in Set.Ioi σ, Real.exp (-Real.pi * (u + ρ) ^ 2) := by
              rw [MeasureTheory.setIntegral_map]
              · rw [Set.preimage_add_const_Ioi]
                ring_nf
              · exact measurableSet_Ioi
              · fun_prop
              · fun_prop
  rw [hsubst]
  -- (2) pointwise comparison on `Ioi σ`
  let c : ℝ := Real.exp (-Real.pi * ρ ^ 2)
  let g0 : ℝ → ℝ := fun u => Real.exp (-Real.pi * u ^ 2)
  let f0 : ℝ → ℝ := fun u => Real.exp (-Real.pi * (u + ρ) ^ 2)
  have hpt (u : ℝ) (hu : u ∈ Set.Ioi σ) : f0 u ≤ c * g0 u := by
    dsimp [f0, g0, c]
    have hu0 : 0 ≤ u := by linarith [hσ, (show σ < u from hu)]
    have hsq2 : u ^ 2 + ρ ^ 2 ≤ (u + ρ) ^ 2 := by nlinarith
    have hexp : -Real.pi * (u + ρ) ^ 2 ≤ -Real.pi * ρ ^ 2 + -Real.pi * u ^ 2 := by
      nlinarith [hsq2, le_of_lt Real.pi_pos]
    calc
      Real.exp (-Real.pi * (u + ρ) ^ 2)
          ≤ Real.exp (-Real.pi * ρ ^ 2 + -Real.pi * u ^ 2) := Real.exp_le_exp_of_le hexp
      _ = Real.exp (-Real.pi * ρ ^ 2) * Real.exp (-Real.pi * u ^ 2) := by
          rw [Real.exp_add]
  -- (3) integrability on `Ioi σ`
  have hpi : 0 < Real.pi := Real.pi_pos
  have hg0_int : IntegrableOn g0 (Set.Ioi σ) := (integrable_exp_neg_mul_sq hpi).integrableOn
  have hcg0_int : IntegrableOn (fun u => c * g0 u) (Set.Ioi σ) :=
    (Integrable.const_mul (integrable_exp_neg_mul_sq hpi) c).integrableOn
  have hf0_int : IntegrableOn f0 (Set.Ioi σ) := by
    dsimp [f0]
    exact ((integrable_exp_neg_mul_sq hpi).comp_add_right ρ).integrableOn
  -- (4) integrate
  have hmono : (∫ u in Set.Ioi σ, f0 u) ≤ (∫ u in Set.Ioi σ, c * g0 u) :=
    MeasureTheory.setIntegral_mono_on hf0_int hcg0_int measurableSet_Ioi hpt
  have hconst : (∫ u in Set.Ioi σ, c * g0 u) = c * (∫ u in Set.Ioi σ, g0 u) := by
    rw [MeasureTheory.integral_const_mul]
  calc
    (∫ u in Set.Ioi σ, Real.exp (-Real.pi * (u + ρ) ^ 2))
        = ∫ u in Set.Ioi σ, f0 u := rfl
    _ ≤ ∫ u in Set.Ioi σ, c * g0 u := hmono
    _ = c * (∫ u in Set.Ioi σ, g0 u) := hconst
    _ = Real.exp (-Real.pi * ρ ^ 2) * (∫ x in Set.Ioi σ, Real.exp (-Real.pi * x ^ 2)) := by
        rfl

end Commons.Analysis.GaussianMeasure