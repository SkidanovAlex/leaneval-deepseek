import Mathlib
import Submission.Commons.Analysis.Complex.jensenCarleman_main

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Jensen–Carleman formula

`Commons.Analysis.Complex.jensenCarleman` — the real-part identity (Heath-Brown 1992,
Lemma 3.2):  for `f` holomorphic on the closed disc around `a` of radius `R`,
non-zero at `a` and on the boundary circle,

`Re (f' a / f a) = -Σ_u divisor(u) · Re(u-a) · (|u-a|⁻² − R⁻²)
                 + (1/(πR)) ∫₀^{2π} cos θ · log |f(a + R e^{iθ})| dθ`.

The statement is proved in the shared commons as
`Commons.Analysis.Complex.jensenCarleman_main` (a full development on top of
`cosAvg_analytic`, `partialX_log_norm`, `sphere_mirror_*`, `zeroFactor_g` and the
harmonic-cosine machinery); this file exposes it under the requested name.
-/

noncomputable section

open Complex Metric MeasureTheory Real Set Topology
open scoped Interval

namespace Commons.Analysis.Complex

theorem jensenCarleman {a : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a |R|))
    (hfa : f a ≠ 0)
    (hfc : ∀ u : ℂ, ‖u - a‖ = R → f u ≠ 0) :
    (deriv f a / f a).re =
      - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) *
          ((u - a).re) * (((‖u - a‖ : ℝ) ^ 2)⁻¹ - (R : ℝ)⁻¹ * (R : ℝ)⁻¹)) +
      (1 / (Real.pi * R)) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos θ * Real.log ‖f (a + (R : ℝ) * Complex.exp (Complex.I * (θ : ℂ)))‖) := by
  exact Commons.Analysis.Complex.jensenCarleman_main hR hf hfa hfc

end Commons.Analysis.Complex
