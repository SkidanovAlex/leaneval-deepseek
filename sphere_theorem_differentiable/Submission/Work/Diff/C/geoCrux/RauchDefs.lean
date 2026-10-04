import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Rauch input of `SphereSizeProp`: the derivative of the geodesic-sphere map

`Work.Diff.C.GeoCrux.SphereSizeProp` (`Submission/Work/Diff/C/geoCrux/FarDefs.lean`) says that two
points at equal distance `ρ ≤ π - arccos (1-c)` from a centre `q` are within `π sin ρ + O(ε₁√c log)`
of each other.  Its proof is the classical Rauch estimate, and this module isolates **the single
analytic input** of that proof, in the form in which it will be used (no parallel transport, no
Jacobi-field vocabulary: the derivative of the sphere map is written as a `curveVelocity`).

## The statement

For a centre `q`, a radius `0 < ρ ≤ π - arccos (1-c)`, and an orthonormal pair `v, w ∈ T_qM`
(`⟪v,v⟫ = ⟪w,w⟫ = 1`, `⟪v,w⟫ = 0`), consider the *great circle of directions*
`σ ↦ cos σ • v + sin σ • w` and the corresponding curve on the geodesic sphere of radius `ρ`,

`Φ σ := GExp q (ρ • (cos σ • v + sin σ • w))`.

Then the speed of `Φ` at `σ = 0` is at most `sin ρ + 16 √ε₁`  (**no factor `ρ`**: on the round unit
sphere `Φ` is the latitude circle of colatitude `ρ`, of radius `sin ρ`, and `Φ'(0) = sin ρ · w`).

## Why this is the right input

`Φ` is exactly the variation of the exponential map along the ray `t ↦ GExp q (t • v)`: writing
`Z(t) := D(GExp q)(t v)[t w]` for the Jacobi field with `Z(0) = 0`, `Z'(0) = w`, one has
`Φ'(0) = Z(ρ)` (both sides are `D(GExp q)(ρ v)[ρ w]`), so `a = ‖Z'(0)‖ = 1`.  The modulus comparison
for that Jacobi field is **already proved** in the workspace:
`Work.Diff.C.jld_modulus_le_sin` (`Diff/C/JacobiModulusRiccati.lean`) gives
`‖Z d‖ ≤ (sin d + 16 √ε) a = sin d + 16√ε` with `ε` the *shape-operator* error of the geodesic
sphere; the shape-operator error from `hHess` is
`Work.Diff.C.rhess_rdist_bound_of_hHess` (`Diff/C/far_sphere_size.lean`, PROVED): on
`{fcos y > -1+c}` (for the centre `y = q`) and for `V ⊥ ∇(rdist q)`,

`|rhess (rdist q)(x) V V - cot (rdist q x) ‖V‖²| ≤ (ε₁ / sin (rdist q x)) ‖V‖²`,

which is the `ε = ε₁` input of `jld_modulus_le_sin`.  Along the ray from `q` to a point at distance
`ρ ≤ π - arccos (1-c)` the points at parameter `t < ρ` have `rdist q (γ t) = t < π - arccos (1-c)`,
so the shape-operator bound **is** available on the whole open interval `(0, ρ)` — no cap crossing is
involved (that only enters the *hinge* bound).  The remaining inputs of `jld_modulus_le_sin` are the
log-derivative identity (`Work.Diff.C.jld_log_norm_hasDerivAt`), the bridge/orthogonality of the
variation field (`Work.Diff.C.dmRadialBridge`, `Work.Diff.C.dmRadialOrthogonal`) and the model
asymptotics at `0⁺` (smoothness of `GExp` in the direction, plus the expansion
`‖J t‖ = ρ t + O(t³)`); all of these are pure calculus about the geodesic flow.

## Inventory of the inputs of `jld_modulus_le_sin` for this `Z` (checked in the workspace)

* `hshape` — `Work.Diff.C.rhess_rdist_bound_of_hHess` (`Diff/C/far_sphere_size.lean`), **PROVED**:
  for the centre `q` and `V ⊥ ∇(rdist q)`,
  `|rhess (rdist q)(x) V V - cot (rdist q x)‖V‖²| ≤ (ε₁ / sin (rdist q x))‖V‖²`, valid on
  `{fcos q > -1+c}` — and along the ray to a point at distance `ρ ≤ π - arccos (1-c)` every interior
  parameter `t < ρ` is in that region.  Use `ε = ε₁`.
* `hlog` — `Work.Diff.C.jld_log_norm_hasDerivAt` (`Diff/C/JacobiLogDeriv.lean`), **PROVED**.
* `hbridge`, `horth` — `Work.Diff.C.dmRadialBridge`, `Work.Diff.C.dmRadialOrthogonal`
  (`Diff/C/dmRadialBridge.lean`), **PROVED** (proved with *no* curvature hypothesis), for the
  variation field `Z t = curveVelocity (fun r => GExp p (t • (u + r • η))) 0`.  Their side
  hypotheses `hsm` (smoothness of `rdist p` at the endpoint), `hrgrad`, `hcsm`, `hne` and
  `hminW` must be supplied.
* the *identification* `Φ'(0) = Z(ρ)` — the classical "the variation field of a family of geodesics
  is the Jacobi field": available in chart form as
  `Submission.ChartGeoAt.variationField_eq_jacobiTensor` (`Submission/ChartGeoAt.lean`, **PROVED**,
  0 sorries) together with the chain rule `Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp`;
  note that at `σ = 0` the *great-circle* family `σ ↦ ρ • (cos σ • v + sin σ • w)` and the *linear*
  family `r ↦ ρ • (v + r • w)` have the same derivative `ρ w`, so the velocity at `σ = 0` is
  `D(GExp q)(ρv)[ρw] = Z(ρ)` for `Z` as in `dmRadialBridge` (with `u := v`, `η := w`).
* **still missing** (the three genuine side conditions):
  (i) `hminW`: `∀ᶠ s in 𝓝 0, rdist q (GExp q (ρ • (v + s • w))) = ‖ρ • (v + s • w)‖`
      (nearby radial rays are minimising up to the radial distance);
  (ii) `hne`/`hpos`: `Z t ≠ 0` for `t ∈ (0,ρ)` (no conjugate point of `q` before `ρ`), which is the
      cut-locus/non-vanishing input (`Submission/ConjCut.lean`'s
      `isInvertible_mfderiv_GExp_of_norm_lt_pi_div_sqrt` gives this in the pinned case);
  (iii) `hasym`: `|‖Z t‖ - t| ≤ C t³` near `0⁺` with `C ≤ 1` (Taylor expansion of the geodesic flow
      at the origin, using a bound on the curvature at `q`).

## From this input to `SphereSizeProp`

Given `z, z'` with `rdist q z = rdist q z' = ρ`, Hopf–Rinow gives minimising rays with unit
directions `v, v'`; joining `v` to `v'` inside the unit sphere by a path of length `≤ π`
(the unit sphere has diameter `π`) and applying the bound above to each (orthonormalised) velocity
along that path bounds the length of the path `s ↦ GExp q (ρ • c(s))` joining `z` to `z'` by
`π (sin ρ + 16 √ε₁)`, hence `rdist z z' ≤ π sin ρ + O(ε₁)`, which is the conclusion of
`SphereSizeProp`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.GeoCrux

/-- **The Rauch bound for the derivative of the geodesic-sphere map.**  For an orthonormal pair
`v, w ∈ T_qM`, the curve `Φ σ = GExp q (ρ • (cos σ • v + sin σ • w))` on the sphere of radius `ρ`
(where `0 < ρ ≤ π - arccos (1-c)`) has speed at most `(sin ρ + 40 (√c + ε₁ π)) ρ` at `σ = 0`.

(The proved modulus comparison `Work.Diff.C.jld_modulus_le_sin` delivers the sharper
`(sin ρ + 16 √ε₁) ρ`; the stated slack is what the downstream statements use.) -/
abbrev RauchSphereMapProp : Prop :=
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
    ∀ (v w : TangentSpace I q),
      Inner.inner ℝ v v = 1 → Inner.inner ℝ w w = 1 → Inner.inner ℝ v w = 0 →
      ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
          (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
            (ρ • (Real.cos σ • v + Real.sin σ • w))) 0‖
        ≤ Real.sin ρ + 40 * (Real.sqrt c + ε₁ * Real.pi)

end Work.Diff.C.GeoCrux
