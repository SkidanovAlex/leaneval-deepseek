import Mathlib
import Submission.Work.RPB1a.Caratheodory.Chord.norm_sub_le_integral_norm_deriv
import Submission.Work.RPB1a.Caratheodory.Chord.circleMap_neg_one_mem_ball

namespace Work.RPB1a.Caratheodory.Chord

open Complex Set Metric MeasureTheory
open scoped ENNReal Real Topology

/-- The chord bound along a circular arc: for a map holomorphic on the unit disc, the distance
between the images of the endpoints of an arc of the circle of radius ρ about -1 that lies inside
the disc is at most ρ times the angular integral of ‖deriv f‖ over the whole period,
the integrand being cut off by the indicator of the unit disc. -/
theorem dist_le_circleMap_chord {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    {ρ θ₁ θ₂ : ℝ} (hρ : 0 < ρ) (hle : θ₁ ≤ θ₂) (hθ₁ : θ₁ ∈ Ioo (-π) π) (hθ₂ : θ₂ ∈ Ioo (-π) π)
    (hc₁ : ρ / 2 < Real.cos θ₁) (hc₂ : ρ / 2 < Real.cos θ₂) :
    ENNReal.ofReal (dist (f (circleMap (-1 : ℂ) ρ θ₁)) (f (circleMap (-1 : ℂ) ρ θ₂))) ≤
      ENNReal.ofReal ρ * ∫⁻ θ in Ioo (-π) π,
        (ball (0 : ℂ) 1).indicator (fun z => ‖deriv f z‖ₑ) (circleMap (-1 : ℂ) ρ θ) := by
  let γ : ℝ → ℂ := circleMap (-1 : ℂ) ρ
  let g : ℝ → ℂ := f ∘ γ
  -- the whole arc lies in the unit disc
  have hball : ∀ θ ∈ Icc θ₁ θ₂, γ θ ∈ ball (0 : ℂ) 1 :=
    fun θ hθ => circleMap_neg_one_mem_ball hρ hle hθ₁ hθ₂ hc₁ hc₂ hθ
  have hdiff : ∀ θ ∈ Icc θ₁ θ₂, DifferentiableAt ℂ f (γ θ) :=
    fun θ hθ => hf.differentiableAt (Metric.isOpen_ball.mem_nhds (hball θ hθ))
  -- chain rule along the circle
  have hderiv : ∀ θ ∈ uIcc θ₁ θ₂,
      HasDerivAt g (deriv f (γ θ) * (circleMap (0 : ℂ) ρ θ * Complex.I)) θ := by
    intro θ hθ
    have hθ' : θ ∈ Icc θ₁ θ₂ := by rwa [Set.uIcc_of_le hle] at hθ
    exact ((hdiff θ hθ').hasDerivAt).comp θ (hasDerivAt_circleMap (-1 : ℂ) ρ θ)
  -- continuity of the derivative of the parametrised curve
  have hcont_derivf : ContinuousOn (deriv f) (ball (0 : ℂ) 1) :=
    (hf.deriv Metric.isOpen_ball).continuousOn
  have h1 : ContinuousOn (fun θ => deriv f (γ θ)) (Icc θ₁ θ₂) :=
    hcont_derivf.comp (continuous_circleMap (-1 : ℂ) ρ).continuousOn
      (fun θ hθ => hball θ hθ)
  have h2 : ContinuousOn (fun θ : ℝ => circleMap (0 : ℂ) ρ θ * Complex.I) (Icc θ₁ θ₂) :=
    ((continuous_circleMap (0 : ℂ) ρ).continuousOn).mul continuousOn_const
  have hcont_g' : ContinuousOn
      (fun θ => deriv f (γ θ) * (circleMap (0 : ℂ) ρ θ * Complex.I)) (Icc θ₁ θ₂) :=
    h1.mul h2
  have hint : IntervalIntegrable
      (fun θ => deriv f (γ θ) * (circleMap (0 : ℂ) ρ θ * Complex.I)) volume θ₁ θ₂ :=
    hcont_g'.intervalIntegrable_of_Icc hle
  -- the mean value estimate: the chord is at most the integral of the speed
  have hmain : ‖g θ₂ - g θ₁‖ ≤ ρ * ∫ θ in θ₁..θ₂, ‖deriv f (γ θ)‖ := by
    have hA := norm_sub_le_integral_norm_deriv hle hderiv hint
    calc ‖g θ₂ - g θ₁‖
        ≤ ∫ x in Set.uIoc θ₁ θ₂, ‖deriv f (γ x) * (circleMap (0 : ℂ) ρ x * Complex.I)‖ := hA
      _ = ∫ x in θ₁..θ₂, ‖deriv f (γ x) * (circleMap (0 : ℂ) ρ x * Complex.I)‖ :=
            by rw [Set.uIoc_of_le hle, intervalIntegral.integral_of_le hle]
      _ = ∫ x in θ₁..θ₂, ρ * ‖deriv f (γ x)‖ := by
            apply intervalIntegral.integral_congr
            intro x _
            simp only [norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos hρ]
            ring
      _ = ρ * ∫ x in θ₁..θ₂, ‖deriv f (γ x)‖ := intervalIntegral.integral_const_mul ρ _
  -- convert the real interval integral into a Lebesgue integral over the whole period
  have hcont_norm : ContinuousOn (fun θ => ‖deriv f (γ θ)‖) (Icc θ₁ θ₂) := h1.norm
  have hint_norm : IntervalIntegrable (fun θ => ‖deriv f (γ θ)‖) volume θ₁ θ₂ :=
    hcont_norm.intervalIntegrable_of_Icc hle
  have hkey : ENNReal.ofReal (∫ θ in θ₁..θ₂, ‖deriv f (γ θ)‖)
      ≤ ∫⁻ θ in Ioo (-π) π, (ball (0 : ℂ) 1).indicator (fun z => ‖deriv f z‖ₑ) (γ θ) := by
    rw [intervalIntegral.integral_of_le hle]
    have hInt : Integrable (fun θ => ‖deriv f (γ θ)‖) (volume.restrict (Ioc θ₁ θ₂)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hint_norm
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc θ₁ θ₂)] fun θ => ‖deriv f (γ θ)‖ :=
      Filter.Eventually.of_forall (fun θ => norm_nonneg _)
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
    calc ∫⁻ θ in Ioc θ₁ θ₂, ENNReal.ofReal ‖deriv f (γ θ)‖
        = ∫⁻ θ in Ioc θ₁ θ₂,
            (ball (0 : ℂ) 1).indicator (fun z => ‖deriv f z‖ₑ) (γ θ) := by
          apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc
          intro θ hθ
          change ENNReal.ofReal ‖deriv f (γ θ)‖ =
            (ball (0 : ℂ) 1).indicator (fun z => ‖deriv f z‖ₑ) (γ θ)
          rw [Set.indicator_of_mem (hball θ (Ioc_subset_Icc_self hθ))]
          simp
      _ ≤ ∫⁻ θ in Ioo (-π) π, (ball (0 : ℂ) 1).indicator (fun z => ‖deriv f z‖ₑ) (γ θ) :=
          MeasureTheory.lintegral_mono_set
            (fun θ hθ => ⟨by linarith [hθ.1, hθ₁.1], by linarith [hθ.2, hθ₂.2]⟩)
  have hdist : dist (f (γ θ₁)) (f (γ θ₂)) = ‖g θ₂ - g θ₁‖ := by
    rw [dist_eq_norm, norm_sub_rev]
    rfl
  calc ENNReal.ofReal (dist (f (γ θ₁)) (f (γ θ₂)))
      = ENNReal.ofReal ‖g θ₂ - g θ₁‖ := by rw [hdist]
    _ ≤ ENNReal.ofReal (ρ * ∫ θ in θ₁..θ₂, ‖deriv f (γ θ)‖) :=
          ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal ρ * ENNReal.ofReal (∫ θ in θ₁..θ₂, ‖deriv f (γ θ)‖) :=
          ENNReal.ofReal_mul hρ.le
    _ ≤ ENNReal.ofReal ρ *
          ∫⁻ θ in Ioo (-π) π, (ball (0 : ℂ) 1).indicator (fun z => ‖deriv f z‖ₑ) (γ θ) :=
          mul_le_mul_right hkey _

end Work.RPB1a.Caratheodory.Chord
