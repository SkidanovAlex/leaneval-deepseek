/-
# The uniform lower bound for the CKMRV divisor on the funnel

The CKMRV interpolation formula has a pole exactly where `j τ = j z`, and the *divisor*
controlling it is `Δ(z) (j τ - j z)`.  The tail expansions of §4.5 need this divisor to be
bounded below by an *absolute* constant — with **no** `τ`-dependent threshold — because the
funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` has only polynomial `scale τ ≍ |τ|`, which cannot absorb the
exponential factor `e^{2π Im τ}` of `j(τ)` (that factor cancels against `q_z = e^{2πiz}`).

Concretely, using `Δ(z) j(z) = E₄(z)³`,

  `Δ(z) (j τ - j z) = Δ(z) j τ - E₄(z)³ = -Sh τ z`,

and `‖Sh τ z‖ ≥ 1/16` on the funnel with `t ≥ Im τ + 1` is
`Work.Asymptotics.funnel_Sh_ge`, proved from the sharp cusp bounds
`‖E₄(z)‖ ≥ 1/2` (`Im z ≥ 3`), `‖Δ(z)‖ ≤ 2 e^{-2πt}`, `‖E₄(τ)‖ ≤ 3/2`,
`‖Δ(τ)‖ ≥ (1/2) e^{-2π Im τ}` and `‖Δ(z) j(τ)‖ ≤ (27/2) e^{-2π(t - Im τ)} ≤ 1/16`.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.funnelTailQuant
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atTop
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Asymptotics.KMinus_funnel_tail_eight
import Submission.Work.Asymptotics.Funnel24Aux

namespace Work.Asymptotics

/-- **Uniform lower bound for the CKMRV divisor on the funnel.**

For `τ` in the funnel and `z = i t` with `t ≥ Im τ + 1` (so that `z` is at distance at least
`1` in the imaginary direction), the divisor `Δ(z)(j τ - j z)` is bounded below by the absolute
constant `1/16`. -/
theorem funnel_divisor_lower :
    ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      (1 / 16 : ℝ) ≤ ‖Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  intro τ z t hτ ht hz
  have h := funnel_Sh_ge τ z t hτ ht hz
  rw [Compact.DeltaFun_mul_sub τ z, norm_neg]
  exact h

end Work.Asymptotics
