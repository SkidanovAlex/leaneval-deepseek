import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.EllSol.FlatFT

/-- If the jointly measurable product `(z,θ) ↦ φ z θ ^ 2 * w θ` is integrable on
`ℝ × Iθ`, then the `z`-energy `θ ↦ (∫ z, φ z θ ^ 2) * w θ` is integrable on `Iθ`.

This is the Fubini/Tonelli "second marginal" statement: the joint integrand is
`(z,θ) ↦ φ z θ ^ 2 * w θ`, whose `z`-integral is `(∫ z, φ z θ ^ 2) * w θ`
(by `integral_mul_const`, and trivially where `w θ = 0`). -/
theorem integrableOn_energy_mul {φ : ℝ → ℝ → ℝ} {w : ℝ → ℝ} (hw : Measurable w)
    (hprod : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (φ p.1 p.2) ^ 2 * w p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (∫ t : ℝ, (φ t θ) ^ 2) * w θ) Work.Spaces.Iθ := by
  -- Step 1: turn the `IntegrableOn (univ ×ˢ Iθ)` hypothesis into integrability for the
  -- product measure `volume.prod (volume.restrict Iθ)`.
  have h1 : Integrable (fun p : ℝ × ℝ => (φ p.1 p.2) ^ 2 * w p.2)
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    hprod
  rw [← Measure.prod_restrict (s := (Set.univ : Set ℝ)) (t := Work.Spaces.Iθ),
    Measure.restrict_univ] at h1
  -- Step 2: Fubini — the second marginal is integrable.
  have hint := h1.integral_prod_right
  -- Step 3: identify the second marginal with the stated function pointwise.
  refine hint.congr (Eventually.of_forall fun θ => ?_)
  show (∫ x : ℝ, (φ x θ) ^ 2 * w θ) = (∫ t : ℝ, (φ t θ) ^ 2) * w θ
  by_cases hw0 : w θ = 0
  · simp [hw0]
  · rw [integral_mul_const]

end Work.FTS.EllSol.FlatFT
