/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted angular interpolation inequality in the *open* class

`thetaInterpCore` is the one-dimensional interpolation inequality

  `∫_{Iθ} (f')² σ ≤ C (∫_{Iθ} f² σ + √(∫_{Iθ} f² σ · ∫_{Iθ} (f'')² σ))`,   `σ = thEta = sin(2θ)^{-η}`,

for a function `f` of class `C²` on the **open** interval `(0, π/2)`, whose three weighted
`L²`-norms are finite, and whose *values* at the two endpoints are `0`.  The traces
`lim_{0⁺} f` and `lim_{(π/2)⁻} f` are **not** assumed to vanish — indeed, by
`thetaInterpEndpoints` they exist and are generally non-zero — so this is the "weak hypothesis"
(the *Core*) version of the paper's §7 slice estimate, designed for the honest class of the
chapter (see `i0Aux/NOTES_interpOpenCore_route.md`).

## Status of the proof

The statement is TRUE.  Numerical evidence (accurate quadrature with the substitution
`θ = t^{1/(1-η)}`, which straightens the integrable singularity of `σ`):

* over a pool of ~500 admissible (i.e. genuinely `C²`) families — the smooth step
  `(F₀ + L₀θ)(1 - H((θ-δ)/r))`, trigonometric families, products of cut-offs — the maximal value
  of `A / (A₀ + √(A₀A₂))` is `≈ 72`;
* the `C²` hypothesis is *essential*: for the non-`C²` "corner" family `L₀·min(θ,δ)` the ratio
  grows like `δ^{-1}` as `δ → 0`, because there `f'` genuinely fails to exist at `θ = δ` (so the
  hypothesis `ContDiffOn ℝ 2 f (Ioo 0 (π/2))` fails, `f''` being a distribution rather than an
  `L²(σ)` function).

## The route (the "flux" form of the identity)

The sub-interval integration by parts `thetaInterpIBPSub` (PROVED) followed by one more
integration by parts of the `cot`-term gives, on every `[a,b] ⊆ (0,π/2)`, the identity

  `A_{a,b} = Φ(b) - Φ(a) - ∫_a^b f f'' σ + 2η ∫_a^b f² σ`,   `Φ := f f' σ + η f² cot(2θ) σ + 2η(1+η) ∫_{θ₀}^{·} cos²(2t) sin(2t)^{-(2+η)} f²`.

Passing to the limit `a → 0⁺`, `b → (π/2)⁻` (the oscillating divergences of `Φ` cancel, using
`σ = sin(2θ)^{-η}` with `η < 1`) gives

  `A = Φ((π/2)⁻) - Φ(0⁺) - ∫_{Iθ} f f'' σ + 2η A₀`,

and the Cauchy–Schwarz bound `|∫ f f'' σ| ≤ √(A₀ A₂)` is *sharp* (it uses the norms of `f`
itself, not those of a modified function).  Since moreover

  `Φ(0⁺) = Γ·F₀·L₀ + ηβ·F₀²`   and   `Φ((π/2)⁻) = -Γ'·F₁·L₁ + ηβ'·F₁²`

with universal constants `Γ, Γ', β, β'` (`F₀,F₁` the traces of `f`, `L₀,L₁` those of `f'`), the
target reduces to the **trace bounds**

  `F₀² + F₁² + |F₀L₀| + |F₁L₁| ≤ C (A₀ + √(A₀A₂))`.

Both are of the "concentration/interpolation" type: from `sliceBoundaryLimit` (PROVED) and the
integrability of the weighted energy one gets, for the trace `F₀` of `f` at `0⁺`,

  `F₀² ≤ C · A₀^{(1+η)/2} · A^{(1-η)/2}`      (`A := ∫_{Iθ} (f')² σ`),

and using the coarse inequality `sliceInterp` (PROVED: `A ≤ 10⁴ (A₀ + A₂)`, valid in the *open*
class with no boundary conditions)

  `F₀² ≤ C (A₀ + A₀^{(1+η)/2} A₂^{(1-η)/2}) ≤ C'(A₀ + √(A₀A₂))`,

since `s^{(1-η)/2} ≤ 1 + s^{1/2}` for `s ≥ 0`.  The *derivative* traces `L₀, L₁` require the
same argument applied to `f'`, which needs, instead of the coarse inequality for `A₂`, a bound
of `A = ∫(f')²σ` by `C(A₀ + √(A₀A₂))` *on the region where the trace is attained*; this is the
remaining gap.

## What is definitely available (PROVED, reusable)

* `Work.EllipticEst.Core.thetaAgmonCompact` — the Agmon (`(1-η)/(1+η)`) slice inequality for
  `C²` functions *supported in a compact sub-interval* of `(0,π/2)`;
* `Work.FTS.EllipticEst.hardy_shift_two_same_weight` — the sharp angular Hardy inequality;
* `Work.FTS.EllipticEst.Honest.sliceInterp` — the coarse weighted interpolation on the open
  interval with **no** boundary conditions;
* `Work.EllipticEst.Core.sliceBoundaryLimit` — existence and decay of the endpoint traces;
* `Work.EllipticEst.Core.thetaInterpEndpoints` — existence of the traces of `f` and `f'`, and
  uniform bounds for them;
* `Work.EllipticEst.Core.thetaInterpIBPSub` — the sub-interval `θ`-integration by parts;
* `Work.FTS.EllipticEst.remov.I1SliceIBP` — the full-interval identity in the closed class.

## ROUTE 2 — this supersedes the flux route above; see `NOTES_thetaInterpCore_ROUTE2.md`

The flux (`Φ`) route is abandoned: it needs the endpoint values `Φ(0⁺) = ΓF₀L₀+ηβF₀²`, hence
bounds on the *derivative* traces `L₀, L₁`, and it is `∞ - ∞ = finite` at every stage.

The correct route is **two steps**:

* **Step 1 (key).** For `u ∈ C²(0,π/2)` whose *traces* vanish at both ends,
  `A(u) ≤ C(P(u) + √(P(u)E(u)))`.  Proof: the **sharp** Hardy
  `∫u²sin^{-(2+η)} ≤ (1/(1+η)²)∫(u')²σ + C∫u²σ` (the constant `1/(1+η)²` is *essential*:
  it gives `2η/(1+η) = 0.995 < 1`), together with the sub-interval IBP
  `A = -∫uu''σ + 2ηP + 2η(1+η)∫u²cos²(2θ)sin^{-(2+η)}` — whose boundary terms
  `[uu'σ + (1/2)u²qσ]` vanish *because* the traces vanish — and Cauchy–Schwarz
  `-∫uu''σ ≤ √(PE)`.  The leftover `(1-η)/(1+η) = 1/199` on `A` gives the constant.
  Delegated as `Work.EllipticEst.Core.i0Aux.traceVanishingInterp` (with
  `openSharpHardy` for the sharp Hardy in the open class).
* **Step 2 (mine).** Reduce the general case to Step 1 by subtracting *bump surrogates*
  `ℓ := F₀·φ₀ + F₁·φ₁` (traces minus the two endpoint bumps), with the bump widths
  `θ₀, θ₁ := min(1/2, (F₀²/(4KA))^{1/(1+η)})` tied to the data
  (`K = 2` from `sliceBoundaryLimit`).  The concentration bound
  `(f θ - F₀)² ≤ 2θ^{1+η}A` gives `P ≥ (F₀²/4)∫_0^{θ₀}σ`, hence `P(f-ℓ) ≤ 18P`; the
  same scale gives `∫ℓ''²σ ≤ 8KA`, hence `E(f-ℓ) ≤ C(P+E)` via `Honest.sliceInterp`; and
  one more IBP (`∫f'ℓ'σ = -∫fℓ''σ + ∫fℓ'qσ`, boundary term zero because `ℓ'` is supported
  in shells away from the endpoints) gives `A(f) ≤ A(f-ℓ) + C(P+√(PE))`.
  Delegated as `thetaInterpCoreOfTraceVanishing`.
-/

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.Core.i0Aux.endpointValuesCore
import Submission.Work.FTS.EllipticEst.remov.I1SliceIBP
import Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight
import Submission.Work.EllipticEst.Core.i0Aux.traceVanishingInterp
import Submission.Work.EllipticEst.Core.i0Aux.thetaInterpCoreOfTraceVanishing

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory Set Filter

theorem thetaInterpCore : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    f 0 = 0 → f (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  exact @Work.EllipticEst.Core.i0Aux.thetaInterpCoreOfTraceVanishing
    (fun _ : ℝ => 0)
    Work.EllipticEst.Core.i0Aux.traceVanishingInterp
    ⟨0, 0, tendsto_const_nhds, tendsto_const_nhds⟩

end Work.EllipticEst.Core.i0Aux
