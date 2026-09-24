import Mathlib
import Submission.RiemannSurface
import Submission.Commons.Geometry.Manifold.chart_transition_analyticOnNhd
import Submission.Work.Drive.phaseGadget
import Submission.Work.Drive.exists_phase_chain_charts
import Submission.Work.Drive.exists_phase_of_chain_charts

/-!
# A continuous global phase with a single simple zero at `z₀` (the "degree-one phase")

## CRITICAL TRAP (found 2026-09-23 by the chain prover, `H1-L26`)

The chain must **not** be formulated with `chartAt ℂ (a i)`: `ChartedSpace.chartAt` is arbitrary
chosen data, and one can chart `ℂ` with `chartAt x := id.restr (ball x (trapRadius x))`
(`trapRadius x = (1 - ‖x‖)/2` inside the unit disc), which is a legitimate
`ChartedSpace ℂ ℂ` + `IsManifold` structure.  There `(chartAt x).source ⊆ unit disc` for every `x`
in the unit disc, so *any* sequence with `a (i+1) ∈ (chartAt ℂ (a i)).source` is trapped in the
compact unit disc and the local-finiteness clause fails.  The counterexample is
`Work.Drive.no_chain_counterexample` in `Submission/Work/Drive/exists_phase_chain_strong.lean`.

**The repair**: the chain lemma must let the prover *choose the charts* out of the (maximal) atlas,
i.e. it must produce
`(a : ℕ → X) (c : ℕ → OpenPartialHomeomorph X ℂ) (ρ : ℕ → ℝ)` with `c i ∈ maximalAtlas` and
`a i, a (i+1) ∈ (c i).source`, `‖(c i)(a i) - (c i)(a (i+1))‖ < ρ i`, the `8 ρ i`-balls locally
finite and well inside the sources.  Likewise `Work.Drive.gadget` must be generalised from
`chartAt ℂ (a i)` to an explicit chart family `c i` (the same proof works verbatim with `c i` in
place of `chartAt ℂ (a i)`; the transition analyticity for two atlas members is the same
`StructureGroupoid.compatible` argument as in
`Submission/Commons/Geometry/Manifold/chart_transition_analyticOnNhd.lean`, and the derivatives
non-vanishing is `Work.Drive.deriv_chart_transition_ne_zero`'s proof with `c i`, `c (i+1)`).

## The construction, in detail (guidance for whoever assembles it)

Input: the escaping chain `a : ℕ → X` with radii `ρ` from `Work.Drive.exists_phase_chain_strong`
(`a 0 = z₀`, `a (i+1)` in the `ρ i`-ball of `a i`, the `8 ρ i`-balls locally finite and well inside
the chart sources, `a` injective).

1. **The gadgets.**  `Work.Drive.gadget a ρ i : X → ℂ` (in `Submission/Work/Drive/phaseGadget.lean`)
   is supported in the chart ball of radius `8 ρ i`, is a unit complex number off the two pivots
   (`Work.Drive.norm_gadget_eq_one`), equals `phase ((z - z(a i))/(z - z(a (i+1))))` in the inner
   ball of radius `2 ρ i` (`Work.Drive.gadget_eq_phase`) and is `1` outside
   (`Work.Drive.gadget_eq_one_of_far`).  It is continuous off its two pivots
   (`Work.Drive.continuousAt_gadget`).

2. **The product.**  `Φ x := ∏ i ∈ {i : x ∈ (8 ρ i)-ball}, gadget a ρ i x` — a *finite* product by
   `hlf` applied to the compact set `{x}` (note `gadget = 1` outside the `8 ρ i`-ball).  Off the
   pivots `Φ` is continuous (locally it is a fixed finite product of continuous factors) and
   `‖Φ x‖ = 1`.  Near a pivot `a j` (`j ≥ 1`) only the two gadgets `j-1`, `j` are discontinuous,
   and their product has a limit `c ≠ 0` (`Work.Drive.pair_gadget_tendsto`, using
   `Work.Drive.tendsto_chart_transition_slope` and `Work.Drive.deriv_chart_transition_ne_zero`).

3. **The radial factor.**  `m : X → ℝ` continuous with `m (z₀) = 0`, `m x > 0` for `x ≠ z₀`, and
   `m x = ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖` near `z₀` (take a chart cut-off
   `χ = clamp ((r - ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖)/ε)` and `m := χ * ‖·‖ + (1 - χ) * 1`).

4. **Filling in the pivots.**  `Ψ := m · Φ`.  Since the limit of `Φ` at each pivot exists and the
   only pivots are the `a i`, define `Θ x := if ∃ i, a i = x then limUnder (𝓝[≠] x) Ψ else Ψ x`.
   Then `Θ` is continuous (at a pivot: `tendsto_nhds_limUnder`; elsewhere `Θ = Ψ` locally and the
   pivots are locally finite), `Θ (z₀) = 0`, and `Θ x ≠ 0` for `x ≠ z₀` (off the pivots `‖Φ‖ = 1`
   and `m > 0`; at the pivots the limit has modulus `1` because `Ψ` is `m ·`(unit) nearby).

5. **The local form at `z₀`.**  Off `z₀`, `Θ x = m x · Φ x`; near `z₀` only gadget `0` is
   non-trivial, and there `gadget 0 x = phase (d x) * phase ((chartAt ℂ (a 0)) x - (chartAt ℂ (a 1)))⁻¹`
   with `d x = (chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀`.  Hence
   `Θ x / d x = phase ((chartAt ℂ (a 0)) x - (chartAt ℂ (a 1)))⁻¹ * (the product of the other
   gadgets)`, which has a continuous non-zero extension to `z₀` (the denominator factor tends to
   `(chartAt ℂ (a 0)) z₀ - (chartAt ℂ (a 0)) (a 1) ≠ 0`).  Take `u` to be that extension on a small
   neighbourhood `V` of `z₀` (with `u (z₀)` the limit) and `u := 1` outside `V`.

-/


open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set Metric
open Classical

namespace Work.Drive

theorem exists_continuous_singleZero_phase {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (hX : ¬ CompactSpace X) (z₀ : X) :
    ∃ Θ : X → ℂ, Continuous Θ ∧ (∀ x : X, x ≠ z₀ → Θ x ≠ 0) ∧
      ∃ (u : X → ℂ) (V : Set X), V ∈ nhds z₀ ∧ ContinuousOn u V ∧ (∀ x ∈ V, u x ≠ 0) ∧
        ∀ x ∈ V, Θ x = ((chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀) * u x := by
  -- The escaping chain of pivots with charts chosen out of the maximal atlas, and the
  -- telescoping product of transfer gadgets attached to that chain.
  obtain ⟨a, c, ρ, hca, ha0, hρ, hchain, hwell, hlf, _hne, hinj⟩ :=
    exists_phase_chain_charts (X := X) hX z₀
  exact exists_phase_of_chain_charts (X := X) z₀ a c ρ hca ha0 hρ hchain hwell hlf hinj

end Work.Drive
