import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_left_mid_delta
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_goodHeight_delta
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_right_logsq
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_left_far_strip_bound_negOne
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_at_height_farLeft_neg_consts_bounded

namespace Commons.NumberTheory.Zeta

/-- Uniform bound for the logarithmic derivative of `ζ₁` on the strip `-1/2 ≤ σ ≤ 2` at a good
height `T ≥ 5`: with an absolute constant `C`,
`‖ζ₁'/ζ₁(σ+iT)‖ ≤ C * ((log (T+3) + 1)^3 + (log (T+3) + 1)^2 / δ)`,
provided no zero of `ζ₁` has imaginary part within `δ` of `T`.

The sub-strip bounds `zeta1_logDeriv_left_mid_delta` (`1/8 ≤ σ ≤ 1/2`),
`zeta1_logDeriv_goodHeight_delta` (`1/2 ≤ σ ≤ 5/8`), `zeta_logDeriv_right_logsq`
(`5/8 ≤ σ ≤ 2`, for `ζ'/ζ`) and `zeta_logDeriv_left_far_strip_bound_negOne`
(`-1 ≤ σ ≤ 1/8`) give this statement piecewise; it is recorded here in the uniform form
`-1/2 ≤ σ ≤ 2` used downstream. Concretely it follows from `zeta1_logDeriv_uniform_b`,
which combines the pieces with the explicit constant `10 ^ 8`. -/
theorem logDeriv_zeta1_strip_goodHeight_le (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ T δ : ℝ, 5 ≤ T → 0 < δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      ∀ σ : ℝ, -(1 / 2 : ℝ) ≤ σ → σ ≤ 2 →
        ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
          C * ((Real.log (T + 3) + 1) ^ 3 + (Real.log (T + 3) + 1) ^ 2 / δ) := by
  refine ⟨(10 : ℝ) ^ 8, by positivity, ?_⟩
  intro T δ hT hδ0 hgood σ hσlo hσhi
  exact zeta1_logDeriv_uniform_b h σ T δ (by linarith) hσhi hT hδ0 hgood

end Commons.NumberTheory.Zeta
