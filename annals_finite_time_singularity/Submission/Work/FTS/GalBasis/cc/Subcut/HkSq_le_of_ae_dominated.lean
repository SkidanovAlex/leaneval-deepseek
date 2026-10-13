import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

/-- **Transfer of an a.e. pointwise bound to the iterated integral.**  If `0 ≤ g ≤ ψ` almost
everywhere on `Iz × Iθ`, `ψ` is nonnegative and measurable on the product, the slices `θ ↦ ψ z θ` are
integrable for a.e. `z`, and the iterated integral `∫_{Iz} ∫_{Iθ} ψ` is finite (i.e.
`z ↦ ∫_{Iθ} ψ z ·` is integrable), then `∫_{Iz} ∫_{Iθ} g ≤ ∫_{Iz} ∫_{Iθ} ψ`.

All three extra hypotheses are needed under Lean's Bochner convention (`integral_undef`: a non-integrable
`ℝ`-valued nonnegative function has integral `0`, not `∞`); the a.e. slice integrability is what
`Work.Spaces.HkMem` provides in applications, and without it the statement is false.

This is the `a.e.` version of `Work.FTS.Nonlinear.N4Fields.HkSq_le_of_integrand_le`, and it is what lets one
apply a pointwise product bound which is only known on the *open* quadrant.  Proof: by Fubini/Tonelli the
first hypothesis gives, for a.e. `z ∈ Iz`, the `θ`-a.e. bound `g z · ≤ ψ z ·`; on that full-measure set of
`z` (intersected with the a.e.-integrability and the finiteness sets) the monotonicity of the integral
(`MeasureTheory.integral_mono_of_nonneg`) gives `∫_{Iθ} g z · ≤ ∫_{Iθ} ψ z ·`, and one more application of
`MeasureTheory.integral_mono_of_nonneg` in `z` (with `hint`) concludes. -/
theorem HkSq_le_of_ae_dominated {g ψ : ℝ → ℝ → ℝ}
    (hg : ∀ z θ : ℝ, 0 ≤ g z θ) (hψ : ∀ z θ : ℝ, 0 ≤ ψ z θ)
    (hψmeas : MeasureTheory.AEStronglyMeasurable (Function.uncurry ψ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hae : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)), g p.1 p.2 ≤ ψ p.1 p.2)
    (hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => ψ z θ) Work.Spaces.Iθ)
    (hint : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ, ψ z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, g z θ)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ψ z θ := by
  -- Fubini step: the product-a.e. bound yields the `θ`-a.e. bound for `z`-a.e. `z`.
  have h1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), g z θ ≤ ψ z θ :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hae
  -- On the (full-measure) set of `z` where both hold, the inner integrals compare.
  have h2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, g z θ) ≤ ∫ θ in Work.Spaces.Iθ, ψ z θ := by
    filter_upwards [h1, hslice] with z hz hzi
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => hg z θ) hzi hz
  -- Outer monotonicity of the integral in `z`, the dominating function being integrable (`hint`).
  exact MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ => hg z θ)
    hint h2

end Work.FTS.GalBasis.cc.Subcut
