import Mathlib

namespace Work.Beltrami

set_option linter.unusedVariables false

open MeasureTheory
open scoped Convolution

/-- Convolution with a probability density `ρ ≥ 0`, `∫ ρ = 1`, preserves the Hölder seminorm:
if `‖f x - f y‖ ≤ K ‖x - y‖ ^ α` for all `x y`, then the same bound holds for `ρ ⋆ f`.

This is the elementary "mollification does not increase the Hölder constant" step used in the
Schauder/Calderón–Zygmund machinery for the Newlander–Nirenberg theorem: writing
`(ρ ⋆ f) x = ∫ t, ρ t • f (x - t)`, the difference of two translates is bounded pointwise by
`ρ t * (K ‖x - y‖ ^ α)` and `∫ t, ρ t * c = c` by `∫ ρ = 1`. -/
theorem convolution_holder_le {ρ : ℂ → ℝ} {f : ℂ → ℂ} {M K α : ℝ} (hK : 0 ≤ K)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρint : ∫ x, ρ x ∂MeasureTheory.volume = 1)
    (hρi : MeasureTheory.Integrable ρ MeasureTheory.volume)
    (hfm : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hfM : ∀ z, ‖f z‖ ≤ M)
    (hholder : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) :
    ∀ x y : ℂ,
      ‖MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
        - MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume y‖
          ≤ K * ‖x - y‖ ^ α := by
  intro x y
  -- `M` is nonnegative since it dominates the norm of `f`.
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hfM 0)
  -- The convolution integrand at a fixed point is integrable: it is dominated by `M * ρ`.
  have hint : ∀ z : ℂ, Integrable (fun t => ρ t • f (z - t)) (volume : Measure ℂ) := by
    intro z
    refine Integrable.mono' (hρi.const_mul M) ?_ ?_
    · exact hρi.aestronglyMeasurable.smul
        (hfm.comp_measurePreserving (Measure.measurePreserving_sub_left volume z))
    · filter_upwards with t
      rw [norm_smul, Real.norm_of_nonneg (hρ0 t), mul_comm M (ρ t)]
      exact mul_le_mul_of_nonneg_left (hfM _) (hρ0 t)
  -- Unfold the convolution as the corresponding integral.
  have hconv : ∀ z : ℂ, MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ)
        (MeasureTheory.volume) z = ∫ t, ρ t • f (z - t) := by
    intro z
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply]
  have hInt : Integrable (fun t => ‖ρ t • f (x - t) - ρ t • f (y - t)‖) (volume : Measure ℂ) :=
    ((hint x).sub (hint y)).norm
  -- The pointwise bound, integrated against the probability measure `ρ`.
  have hbound : ∫ t, ‖ρ t • f (x - t) - ρ t • f (y - t)‖ ≤ K * ‖x - y‖ ^ α := by
    calc ∫ t, ‖ρ t • f (x - t) - ρ t • f (y - t)‖
        ≤ ∫ t, ρ t * (K * ‖x - y‖ ^ α) := by
          refine integral_mono_ae hInt (hρi.mul_const _) ?_
          filter_upwards with t
          have h1 : ρ t • f (x - t) - ρ t • f (y - t)
              = ρ t • (f (x - t) - f (y - t)) := by
            rw [smul_sub]
          rw [h1, norm_smul, Real.norm_of_nonneg (hρ0 t)]
          have h2 : ‖f (x - t) - f (y - t)‖ ≤ K * ‖x - y‖ ^ α := by
            have := hholder (x - t) (y - t)
            rwa [show (x - t) - (y - t) = x - y by ring] at this
          exact mul_le_mul_of_nonneg_left h2 (hρ0 t)
      _ = (∫ t, ρ t) * (K * ‖x - y‖ ^ α) := integral_mul_const _ _
      _ = K * ‖x - y‖ ^ α := by rw [hρint, one_mul]
  calc ‖MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
        - MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume y‖
      = ‖∫ t, (ρ t • f (x - t) - ρ t • f (y - t))‖ := by
        rw [hconv x, hconv y, ← integral_sub (hint x) (hint y)]
    _ ≤ ∫ t, ‖ρ t • f (x - t) - ρ t • f (y - t)‖ := norm_integral_le_integral_norm _
    _ ≤ K * ‖x - y‖ ^ α := hbound

end Work.Beltrami
