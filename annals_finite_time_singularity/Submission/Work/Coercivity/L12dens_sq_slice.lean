import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FM.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.Coercivity.K_facts
import Submission.Work.Coercivity.slice_cs_K

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set

/-- The squared angular density `L₁₂^K(f)(z) = (1/z)∫_θ K(θ) f(z,θ) dθ` of the fundamental
model is controlled by the angular energy of the slice: for `z > 0`,
`(L₁₂^K(f)(z))² ≤ 3 (∫_θ f(z,θ)² dθ)/z²`.

This is the Cauchy–Schwarz inequality for the weight `K(θ) = 3 sin θ cos²θ` on
`Iθ = [0,π/2]` (whose `L²`-norm on the slice is at most `3 = ‖K‖_∞`), together with the
elementary identity `L₁₂^K(f)(z) = (1/z)∫_θ K(θ) f(z,θ) dθ`.  The normalisation
`∫_θ K = 1` is not needed for the estimate. -/
theorem L12dens_sq_slice (f : ℝ → ℝ → ℝ)
    (hK : ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ = (1 : ℝ)) {z : ℝ} (hz : 0 < z)
    (hsl : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Work.Spaces.Iθ) :
    (Work.FM.L12dens Work.Spaces.K f z) ^ 2
      ≤ 3 * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z ^ 2 := by
  -- Cauchy–Schwarz on the angular slice, against the weight `K`.
  have hcs : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f z θ) ^ 2
      ≤ 3 * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 :=
    slice_cs_K f z K_facts_nonneg K_facts_sq_integrableOn K_facts.2.2.2 hsl
  -- `L₁₂^K(f)(z)` is `(1/z)` times that angular integral, and `z > 0`.
  rw [Work.FM.L12dens, MeasureTheory.integral_div, div_pow]
  exact div_le_div_of_nonneg_right hcs (by positivity)

end Work.Coercivity
