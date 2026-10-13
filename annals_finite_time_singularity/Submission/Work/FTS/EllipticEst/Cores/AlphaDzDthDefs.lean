/-
Copyright: work module for the Elgindi finite-time singularity project.

# Vocabulary and route for the target `Cores.AlphaDzDth_ellT`

Target (`Submission/Work/FTS/EllipticEst/Cores/AlphaDzDth_ellT.lean`): for `k ≥ 2` there is a
universal `C > 0` with

  `α · |D_z ∂_θ Ξ|_{ℋ^k} ≤ C (|F|_{ℋ^k} + |∂_θ² Ξ|_{ℋ^k} + α² |z²∂_zzΨ|_{ℋ^k})`,
  `Ξ = EllResid α F Ψ`,

for every `0 < α ≤ 1/4` and every datum of the trace-free class `EllHypT α k F Ψ` satisfying
`OrthCond (Ψ + Gsing α F · sin 2θ)`.

This module collects the *vocabulary* used by the pieces of the proof (`Vfts`, `GBfts`) — it
contains no `sorry` and no proof obligation of its own, so that the sibling modules proved by the
fleet can import it without inheriting `sorryAx`.

## The route (paper §'Elliptic Regularity Estimates', organised as in `Work.Blocks.alphaDzDth_le`)

Write

* `V := Vfts α F Ψ = fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)` — the
  *straightened* solution (so `bslOp α V = orthSource F` and `V = Ξ + Ḡ·sin 2θ` with
  `Ḡ := Gbar α F`), and
* `GB := GBfts α F = fun z θ => 2 cos(2θ) · (α · z ∂_z Ḡ(z))`.

Since `Ξ = V - Ḡ·sin 2θ`, the product rule gives, on the open quadrant,

* `∂_θ Ξ = ∂_θ V - 2 cos(2θ) · Ḡ`, hence
* `D_z ∂_θ Ξ = D_z ∂_θ V - 2 cos(2θ) · (z ∂_z Ḡ)`,
* `α D_z ∂_θ Ξ = α D_z ∂_θ V - GB`.

The estimate is then the triangle inequality (`HkNorm_add_fts` / `HkNorm_add_le`) plus the four
estimates

| # | statement | module |
|---|---|---|
| (A) | `α\|D_z∂_θV\| ≤ C (α²\|D_z²V\| + \|∂_θ²V\| + α\|D_zV\|)` (interpolation core) | `honest_alphaDz_pth_core` |
| (B) | `α²\|D_z²V\| + 5α\|D_zV\| ≤ C(\|F\| + \|∂_θ²Ξ\| + α²\|z²∂_zzΨ\|)` (straight estimate) | `honest_straight_DzV` |
| (C) | `\|∂_θ²V\| ≤ C(\|F\| + \|∂_θ²Ξ\|)` (`Ḡ`-layer transfer) | `honest_pthIter2_Vfts_le` |
| (D) | `HkMem (GB) ∧ \|GB\| ≤ C\|F\|` (`Ḡ`-layer) | `honest_GBfts_mem_le` |

plus the membership `HkMem α k (D_z∂_θV)` (`honest_Vfts_mems`) needed by the triangle
inequality.

## The key structural input for (A): vanishing `θ`-traces

The one piece that has no counterpart in the workspace's `EllHyp`-chain is (A): in the
class `EllHypT` the datum is only `C^∞` on the *open* quadrant, so the angular integrations by
parts that the strip-class proof of `Work.Blocks.alphaDz_pth_core_strip` performs slicewise have
to be replaced by sub-interval integrations plus a limit.  What makes this work is that in this
application the relevant slices have **vanishing traces**: under `OrthCond` one has
`V = Ψ - (15/4)·F_*(Ψ)·sin 2θ` (`Cores.DiagEstEllT.honest_Gsing_eq_neg_fstar_Psi`), and the
"moment ladder" argument of `Cores/OrthCond_lambda_zero.lean` (generalised to the `D_z`-iterates
of `Ψ`: `D_z` commutes with the Euler operator `α²z²∂_z² + α(5+α)z∂_z`, hence `D_z^jGsing`
satisfies the same ODE with source `(15/4)F_*(D_z^jF)`, and the boundary term of the angular
integration by parts against the adjoint kernel `sinθcos²θ` is exactly the trace of `D_z^jΨ`)
gives

  `lim_{θ→0⁺} D_z^jΨ(z,θ) = 0`  and  `lim_{θ→π/2⁻} D_z^jΨ(z,θ) = 0`  for every `j`

(`honest_DzTrace_Vfts_zero` below), hence the same for `D_z^jV`.

With vanishing traces, the *sharp* angular Hardy identity

  `4η ∫_a^b σ_{2+η} f² = ∫_a^b σ (f')² - ∫_a^b σ (f' - 2η cot(2θ) f)² - 2η [cot(2θ) σ f²]_a^b`,
  `σ = sin(2θ)^{-η}`,  `σ_{2+η} = sin(2θ)^{-(2+η)}`

(valid for every `f` of class `C¹` on `(0,π/2)`, `0 < a < b < π/2`; see
`Submission/Work/EllipticEst/Core/hardySigmaBoundary.lean`) has *both* boundary terms tending to
`0` along `a↓0`, `b↑π/2` (both are `o(1)` as soon as `f² = o(θ^{1+η})` at the endpoints), so

  `4η ∫_0^{π/2} σ_{2+η} f² ≤ ∫_0^{π/2} σ (f')²`

with the *sharp* constant `1/(4η)` — exactly the input
`2η(η+1)·(1/(4η)) = (η+1)/2 < 1` that the volume (θ then z) integration by parts of (A) needs in
order to absorb the `σ_{2+η}`-term into the left-hand side.  (For `η = 99/100` the slack is
`(1-η)/2 = 1/200`.)
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

set_option autoImplicit false

/-- The *straightened* datum of the elliptic chapter: `V = Ψ + Gsing α F · sin 2θ`.
It satisfies `V = Ξ + Ḡ · sin 2θ` (`Ḡ = Gbar α F`) and `bslOp α V = orthSource F`. -/
abbrev Vfts (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)

/-- The `Ḡ`-layer correction `GB = 2 cos(2θ) · (α · z ∂_z Ḡ)` occurring in the identity
`α D_z∂_θΞ = α D_z∂_θV - GB`. -/
abbrev GBfts (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * Real.cos (2 * θ) * (α * (z * deriv (Work.Elliptic.Gbar α F) z))

end Work.FTS.EllipticEst.Cores
