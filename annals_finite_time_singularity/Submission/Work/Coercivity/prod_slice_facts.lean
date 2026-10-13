import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory

/-- Fubini/Tonelli bookkeeping for the weight `w`: from joint integrability of
`(z,θ) ↦ (f z θ * w z)²` on `Iz ×ˢ Iθ` one gets a.e. integrability of the `θ`-slices, the
integrability of `z ↦ ∫ θ in Iθ, (f z θ * w z)²`, and the pointwise identity
`∫ θ in Iθ, (f z θ * w z)² = (w z)² * ∫ θ in Iθ, (f z θ)²` (no integrability needed for the
last one, by `MeasureTheory.integral_const_mul`).

Intended proof: `Measure.volume_eq_prod` followed by `← Measure.prod_restrict` rewrites the
hypothesis as `Integrable g ((volume.restrict Iz).prod (volume.restrict Iθ))`; then
`Integrable.prod_left_ae` and `Integrable.integral_prod_left` give the first two conjuncts,
and the third is `MeasureTheory.integral_const_mul` plus pointwise `ring`. -/
theorem prod_slice_facts (f : ℝ → ℝ → ℝ)
    (hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
        MeasureTheory.Integrable (fun θ => (f z θ * Spaces.w z) ^ 2)
          (MeasureTheory.volume.restrict Spaces.Iθ)) ∧
      MeasureTheory.Integrable (fun z => ∫ θ in Spaces.Iθ, (f z θ * Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Spaces.Iz) ∧
        (∀ z, (∫ θ in Spaces.Iθ, (f z θ * Spaces.w z) ^ 2)
          = (Spaces.w z) ^ 2 * ∫ θ in Spaces.Iθ, (f z θ) ^ 2) := by
  have hg : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2))
      ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact hfw
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.uncurry] using hg.prod_right_ae
  · simpa [Function.uncurry] using hg.integral_prod_left
  · intro z
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    ring

end Work.Coercivity
