import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS_StreamBdry.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.UprimeAux.Defs` — the weight `wfun` of the singular `θ`-ODE

The lemma `Work.FTS_StreamBdry.SB6.uprime_le` bounds `∂_θ u` where

  `u(z,θ) = psiP αG Ψ z θ / sin 2θ`   on `Qd = (0,∞) × (0,π/2)`,

i.e. the `θ`-derivative of the `U`-slot part of the stream function divided by `sin 2θ`.  The
content is the ground-state ODE of `Work.FTS_StreamBdry.SB3.P2Aux.bslOp_div_s2_hasDerivAt`:
on `Qd`

  `u'' + c(θ) u' = H`,   `c(θ) = 4 cos 2θ / sin 2θ - tan θ`,

with `|H| ≤ A / sin 2θ + C`.  The integrating factor of this singular equation is
`exp (∫ c) = sin²(2θ) cos θ = 4 wfun θ` with

  `wfun θ = sin²θ · cos³θ`,

which vanishes like `θ²` at `θ = 0` and like `(π/2 - θ)³` at `θ = π/2`.  Consequently
`G := wfun · u'` satisfies `G' = wfun · H`, hence `G` is controlled by
`gwt A C θ = wfun θ · (A / sin 2θ + C) = A·wfun θ/sin 2θ + C·wfun θ`, and the two endpoints are
harmless because `wfun θ / sin 2θ = sin θ cos²θ / 2` is *bounded* (indeed `→ 0`).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB6.UprimeAux

set_option autoImplicit false

/-- The integrating factor weight `wfun θ = sin²θ·cos³θ` of the singular `θ`-equation:
`wfun' = wfun · (4 cos 2θ / sin 2θ - tan θ)` on `(0, π/2)`. -/
def wfun (θ : ℝ) : ℝ := Real.sin θ ^ 2 * Real.cos θ ^ 3

/-- The pointwise bound function for the right hand side: with `|H| ≤ A/sin 2θ + C` one has
`|wfun · H| ≤ gwt A C`. -/
def gwt (A C θ : ℝ) : ℝ := A * (wfun θ / Real.sin (2 * θ)) + C * wfun θ

@[simp] theorem wfun_def (θ : ℝ) : wfun θ = Real.sin θ ^ 2 * Real.cos θ ^ 3 := rfl
@[simp] theorem gwt_def (A C θ : ℝ) :
    gwt A C θ = A * (wfun θ / Real.sin (2 * θ)) + C * wfun θ := rfl

end Work.FTS_StreamBdry.SB6.UprimeAux
