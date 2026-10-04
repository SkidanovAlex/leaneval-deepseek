import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The geometric core of the classical endgame: the two hard inputs of `perimeter_bound`

This module packages, as closed `Prop`-valued `abbrev`s (in the style of
`Submission.Work.Diff.C.GeoCrux.Defs`), the two geometric statements that the proof of
`Work.Diff.C.GeoCrux.perimeter_bound` needs, so that they can be *delegated*: the harness
elaborates a submitted statement in a file that has only the `depends_on` imports and no `open`
commands, and in that bare context the Riemannian-bundle binders of a direct statement do not
elaborate.

## The two inputs

* `SphereSizeProp` — **the geodesic-sphere size bound** (Rauch comparison).  Under the hypotheses
  `hHess`/`hgrad`/`hsmC`/`hcont` ("the metric is a round unit sphere of error `ε₁`, on the region
  `fcos q > -1+c`"), two points at *equal* distance `ρ ≤ π - arccos (1-c)` from `q` are within
  `π sin ρ + O(ε₁ √c log(1/(c ε₁)))` of each other.  This is the classical Rauch estimate
  `diam S(q,ρ) ≤ π sin ρ`: the Jacobi field `J` along a ray from `q` with `J(0) = 0` satisfies
  `‖J(ρ)‖ ≤ (sin ρ + o(1))‖J'(0)‖`, and integrating over the unit sphere of directions (diameter
  `π`) gives the bound.  The machinery lives in the workspace:
  `Work.Diff.C.rhess_rdist_bound_of_hHess` (the shape-operator bound from `hHess`),
  `Work.Diff.C.dmRadialBridge`/`dmRadialOrthogonal` (the bridge `⟨∇_t Z, Z⟩ = rhess (rdist q)(Z,Z)`
  for the radial variation field — proved *without* curvature hypotheses), and
  `Work.Diff.C.jld_modulus_le_sin` (the Sturm/Riccati comparison for the modulus of a Jacobi
  field with `J(0) = 0`).

* `HingeCosProp` — **the crude hinge comparison in the `cos` form**.  For a *unit-speed ray*
  `σ s = GExp x (s • u)` (any `s ∈ [0,π]`, `u` unit, `GExp` the global exponential map based at
  `x`) and a centre `y`, one has
  `cos (rdist y (σ s)) ≥ cos (rdist x y + s) - K (c + ε₁ π)`.
  In the round unit sphere this holds *exactly* (`K = 0`): the law of cosines gives
  `cos b = cos a cos c + sin a sin c cos θ ≥ cos a cos c - sin a sin c = cos (a+c)`, and indeed one
  checks that a ray through the antipode of `y` realises equality at every `s`.  The proof in the
  general (nearly round) case is the ODE comparison `(cos ∘ ρ)'' + (cos ∘ ρ) ≥ -ε₁` along the ray
  (this is exactly `hHess` pulled back to the ray, valid while `ρ < π - δ`), together with a
  treatment of the part of the ray inside the antipodal cap `{rdist y · ≥ π - δ}`: the ray crosses
  the cap in an arc of length `≤ π sin(π-δ) + o(1)` (the `SphereSizeProp` bound), and the phase
  bookkeeping across that arc costs only `O(c)`.  The case `a + s ≥ π` of the conclusion is
  `≤ 1`, hence `O(c)`-sharp.

Both statements are *true* (they are classical comparison-geometry facts, and the round sphere
satisfies them with error `0`), and neither is vacuous: with `ε₁ = 0` and any admissible `c > 0` the
round unit sphere realises both hypotheses and both bounds.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.GeoCrux

/-- **The geodesic-sphere size bound.**  Two points at distance exactly `ρ` from `q`
(`0 < ρ ≤ π - arccos (1-c)`) are within `π sin ρ` up to a correction `O(ε₁ √c log(1/(c ε₁)))`. -/
abbrev SphereSizeProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi),
    ∀ (q : M) (ρ : ℝ), 0 < ρ → ρ ≤ Real.pi - Real.arccos (1 - c) →
    ∀ z z' : M, rdist (I := I) (M := M) q z = ρ →
      rdist (I := I) (M := M) q z' = ρ →
      rdist (I := I) (M := M) z z'
        ≤ Real.pi * Real.sin ρ
          + 100 * ε₁ * Real.sqrt c * (1 + Real.log (1 / (c * ε₁)))

/-- **The crude hinge comparison in the `cos` form.**  For a unit-speed ray
`σ s = GExp x (s • u)` and a centre `y`,
`cos (rdist y (σ s)) ≥ cos (rdist x y + s) - K (c + ε₁ π)`, with the constant `K = 40`. -/
abbrev HingeCosProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi),
    ∀ (x y : M) (u : TangentSpace I x) (s : ℝ),
      Inner.inner ℝ u u = 1 → 0 ≤ s → s ≤ Real.pi →
      Real.cos (rdist (I := I) (M := M) y
          (Submission.GlobalExp.GExp (cov := cov) hmet x (s • u)))
        ≥ Real.cos (rdist (I := I) (M := M) x y + s)
          - 40 * (c + ε₁ * Real.pi)

end Work.Diff.C.GeoCrux
