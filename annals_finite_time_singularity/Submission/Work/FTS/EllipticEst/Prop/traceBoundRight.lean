import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.i0Aux.endpointValuesCore
import Submission.Work.EllipticEst.Core.i0Aux.traceVanishingInterp
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit
import Submission.Work.FTS.EllipticEst.Prop.TraceDefs
import Submission.Work.FTS.EllipticEst.Prop.TraceValueRight
import Submission.Work.FTS.EllipticEst.Prop.TraceFluxAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open MeasureTheory

/-- **The trace bound at the right endpoint `θ = (π/2)⁻`.**

For `f` of class `C²` on the open interval `(0, π/2)` whose one-sided limits `F₁ = lim f` and
`L₁ = lim f'` at `(π/2)⁻` exist, and whose weighted `L²`-energies
`A = ∫_{Iθ} f² · thEta`, `B = ∫_{Iθ} (f'')² · thEta` (`thEta θ = sin(2θ)^{-η}`, `η = 99/100`)
are finite, one has

`max (-(F₁ L₁)) 0 + F₁² ≤ C (A + √(A B))`.

The two summands are the two halves of the estimate:
* `TraceValueRight` gives `F₁² ≤ 100 (A + √(A B))` from the two-scale endpoint estimate
  `EndpointValues.endpointParamRight` and the one-dimensional optimisation
  `EndpointValues.endpointSqBound` (no trace at `θ = 0` is needed);
* `TraceFluxAux` gives `-(F₁ L₁) ≤ √(A B) + K A`: integrate the identity
  `(f f')' = (f')² + f f''` against the cutoff `χ = TraceDefs.chi` (which vanishes near `0` and
  equals `1` near `π/2`), so that the boundary term at `(π/2)⁻` is exactly `F₁ L₁`, bound the
  cross term by Cauchy–Schwarz and the truncation error by `K A` (`K` from `chi_deriv_bdd`). -/
theorem traceBoundRight : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (F₁ L₁ : ℝ),
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁) →
    Filter.Tendsto (deriv f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L₁) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    max (-(F₁ * L₁)) 0 + F₁ ^ 2
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := TraceValueRight
  obtain ⟨K, hK0, hK⟩ := TraceFluxAux
  refine ⟨C₁ + K + 1, by linarith, ?_⟩
  intro f F₁ L₁ hf hF hL hA hD hB
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hAdef
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
    with hBdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
  have hsqrt0 : 0 ≤ Real.sqrt (A * B) := Real.sqrt_nonneg _
  have hval := hC₁ f F₁ hf hF hA hB
  rw [← hAdef, ← hBdef] at hval
  have hflux := hK f F₁ L₁ hf hF hL hA hB
  rw [← hAdef, ← hBdef] at hflux
  have hAB : 0 ≤ A + Real.sqrt (A * B) := by linarith
  have hmax : max (-(F₁ * L₁)) 0 ≤ Real.sqrt (A * B) + K * A :=
    max_le hflux (by nlinarith [hsqrt0, hA0, hK0])
  have hX : max (-(F₁ * L₁)) 0 ≤ (K + 1) * (A + Real.sqrt (A * B)) := by
    refine le_trans hmax ?_
    nlinarith [hsqrt0, hA0, hK0, hAB]
  have hY : F₁ ^ 2 ≤ C₁ * (A + Real.sqrt (A * B)) := by
    nlinarith [hval, hC₁pos, hAB]
  calc max (-(F₁ * L₁)) 0 + F₁ ^ 2
      ≤ (K + 1) * (A + Real.sqrt (A * B)) + C₁ * (A + Real.sqrt (A * B)) := add_le_add hX hY
    _ = (C₁ + K + 1) * (A + Real.sqrt (A * B)) := by ring

end Work.FTS.EllipticEst.Prop
