import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.DivQ.sqIntervalIntegralLe
import Submission.Work.FTS.H2.DivQ.derivIntegrablePrimitive
import Submission.Work.FTS.H2.DivQ.sqIntegral_le_weightedIntegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter

/-- **Pointwise Poincaré for an honest slice.**  If `h` is smooth on the open angular interval
`(0, π/2)`, tends to `0` at the left endpoint `0`, and the weighted square `(h')² · sin(2θ)^{-η}`
is integrable on `Iθ = [0, π/2]` (`η = Work.Spaces.eta = 99/100`), then for every `θ ∈ (0, π/2)`

  `(h θ)² ≤ C · ∫_{Iθ} (h')² · sin(2θ)^{-η}`

with a universal constant `C`.  (The value `π/2` works: `h θ = ∫_0^θ h'`, so
`(h θ)² ≤ θ · ∫_0^θ (h')² ≤ (π/2) · ∫_{Iθ} (h')² ≤ (π/2) · ∫_{Iθ} (h')² sin(2θ)^{-η}`, the last
step because `sin(2θ)^{-η} ≥ 1` on the open interval.)  Only the left endpoint limit is needed. -/
theorem honestPoincarePoint :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (h θ) ^ 2 ≤ C *
          (∫ x in Work.Spaces.Iθ,
            (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))) := by
  refine ⟨Real.pi / 2, by positivity, ?_⟩
  intro h hsm hten hint θ hθ
  -- integrability of `(h')²` and `h'` on `(0, θ]`, interval integrability, and the primitive form
  obtain ⟨hint2Ioc, _hderivIoc, hI1, hI2, hFTC⟩ := derivIntegrablePrimitive hθ hsm hten hint
  -- Cauchy–Schwarz against the constant function `1`
  have hCS := sqIntervalIntegralLe (deriv h) hθ.1.le hI1 hI2
  -- `∫_0^θ (h')² ≤ ∫_{Iθ} (h')² sin(2θ)^{-η}`
  have hmono := sqIntegral_le_weightedIntegral hθ hint hint2Ioc
  have hnn : 0 ≤ ∫ x in (0 : ℝ)..θ, (deriv h x) ^ 2 :=
    intervalIntegral.integral_nonneg_of_ae hθ.1.le (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have hBnn : 0 ≤ ∫ x in Work.Spaces.Iθ,
      (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := le_trans hnn hmono
  rw [hFTC]
  calc (∫ x in (0 : ℝ)..θ, deriv h x) ^ 2
      ≤ θ * ∫ x in (0 : ℝ)..θ, (deriv h x) ^ 2 := by simpa using hCS
    _ ≤ θ * (∫ x in Work.Spaces.Iθ,
          (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_left hmono (le_of_lt hθ.1)
    _ ≤ (Real.pi / 2) * (∫ x in Work.Spaces.Iθ,
          (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_right hθ.2.le hBnn

end Work.FTS.H2.DivQ
