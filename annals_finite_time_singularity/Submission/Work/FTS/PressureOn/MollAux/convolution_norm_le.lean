import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.FTS.PressureOn.MollDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

/-- **Norm bound for a convolution with a probability density.**

If `ρ ≥ 0` is integrable with `∫ ρ = 1` and `‖g y‖ ≤ Vd` for all `y`, then the convolution
`ρ ⋆[lsmul ℝ ℝ, volume] g` (i.e. `x ↦ ∫ t, ρ t • g (x - t)`) is bounded by `Vd` pointwise:
`‖∫ t, ρ t • g (x - t)‖ ≤ ∫ t, ρ t * ‖g (x - t)‖ ≤ Vd * ∫ t, ρ t = Vd`. -/
theorem convolution_norm_le (ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hρ : ∀ z, 0 ≤ ρ z) (hρint : MeasureTheory.Integrable ρ MeasureTheory.volume)
    (hint : ∫ z, ρ z = 1) (hg : Continuous g) (hgc : HasCompactSupport g)
    (Vd : ℝ) (hVd : ∀ y, ‖g y‖ ≤ Vd) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖MeasureTheory.convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x‖ ≤ Vd := by
  -- rewrite the convolution as the Bochner integral `∫ t, ρ t • g (x - t)`
  rw [MeasureTheory.convolution_lsmul]
  -- pointwise bound on the integrand
  have hb : ∀ t, ‖ρ t • g (x - t)‖ ≤ ρ t * Vd := by
    intro t
    rw [norm_smul, Real.norm_of_nonneg (hρ t)]
    exact mul_le_mul_of_nonneg_left (hVd (x - t)) (hρ t)
  have hInt : MeasureTheory.Integrable (fun t => ρ t * Vd) MeasureTheory.volume :=
    MeasureTheory.Integrable.mul_const hρint Vd
  calc ‖∫ t, ρ t • g (x - t)‖ ≤ ∫ t, ρ t * Vd :=
        MeasureTheory.norm_integral_le_of_norm_le hInt (Filter.Eventually.of_forall hb)
    _ = Vd := by rw [MeasureTheory.integral_mul_const, hint, one_mul]

end Work.FTS.PressureOn.MollAux
