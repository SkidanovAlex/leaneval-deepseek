import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two geometric inputs of `Work.Diff.C.GeoCrux.RauchSphereMapProp`

`Work.Diff.C.GeoCrux.RauchSphereMapProp` (`geoCrux/RauchDefs.lean`) bounds the speed at `σ = 0` of the
geodesic-sphere map `σ ↦ GExp q (ρ • (cos σ • v + sin σ • w))` by `sin ρ + 40 (√c + ε₁ π)`.

Its proof (spelled out in `RauchDefs.lean`) is the modulus comparison `Work.Diff.C.jld_modulus_le_sin`
for the radial variation field

`Z t = curveVelocity (fun r => GExp q (t • (v + r • w))) 0`

(the Jacobi field along the ray `t ↦ GExp q (t • v)` with `Z 0 = 0`), for which the derivative of the
sphere map is `Z ρ`.

All the *calculus* of that proof is local: the bridge `⟨∇_t Z, Z⟩ = Hess (rdist q) (Z, Z)`
(`Work.Diff.C.dmRadialBridge`), the shape-operator bound `|Hess (rdist q) - cot t · g| ≤ ε₁/sin t`
(`Work.Diff.C.rhess_rdist_bound_of_hHess`) and the Sturm/Grönwall comparison.  What is **not** local,
and what this module isolates so that it can be delegated, are two geometric facts about the ray
`t ↦ GExp q (t • v)` for `t` up to `L := π - arccos (1 - c)`:

* `CutInjectProp` — the exponential map at `q` is injective on the ball of radius `L`, i.e. **no point
  of the ray stops being minimising before `L`**.  Equivalently `cutTime q ξ ≥ L` for every unit `ξ`.
  This is what supplies `rdist q (GExp q X) = ‖X‖` for `‖X‖ < L`, hence both the minimising identity
  `rgrad (rdist q) (γ t) = γ' t` used by `dmRadialBridge` and the hypothesis `hminW` of that lemma
  (which is about the *perturbed* rays `s ↦ GExp q (t • (v + s • w))`, of length `< L` for `t < L`).

  Its proof is the classical cut-locus argument: a cut point at distance `≤ L` is either *tangential*
  (two distinct minimising geodesics) or *conjugate*; the first is excluded by the chain rule along
  both rays together with the smoothness of `rdist q` on the region `{fcos q ≥ -1 + c}` (which is
  `hsmC`), the second by `Work.Diff.C.no_conjTime_le_arccos` (proved) fed with the bridge and the
  two-sided shape-operator bound `rhess_rdist_bound_of_hHess` (proved).  The library has all the
  cut-point machinery: `Submission.CutTime`, `Submission.InjRadius`,
  `Submission.CutStep2.exists_two_minimising_of_not_injAtLeast`,
  `Submission.InjRadiusCut.exists_cutTime_lt_of_not_injAtLeast`,
  `Submission.CutKlingenberg.exists_two_minimising_or_not_locallyInjective_of_cutTime`,
  `Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast`.

* `RadialModulusProp` — the modulus of the radial variation field `Z` stays within a factor `16` of the
  round-sphere model `sin t`, on the whole interval `(0, L)`.  This packages the two remaining
  analytic facts of the comparison: the field **does not vanish** on `(0, L)` (so that `log ‖Z‖` is
  defined, and `modulus_le_sin_add_sqrt` applies) and the **anchor** — the model asymptotics
  `‖Z t‖ ≈ sin t` at the *scale* `√(c/4)` where the comparison has to be started (a fixed-constant
  `O(t³)` asymptotics on a *neighbourhood of `0`* is *not* available from the hypotheses: the
  hypotheses constrain the *shape operator* of the geodesic spheres, which at scale `t` bounds the
  curvature only through the weighted averages appearing at scale `t`, and the integral
  `∫_0^t (S - cot)` that defines `log (‖Z t‖/sin t)` is only controlled through the two-sided bound
  at *every* scale `0 < s ≤ t`).  With `CutInjectProp` the shape-operator bound gives
  `(log ‖Z t‖)' ≤ cot t + ε₁/sin t` on `(0, L)`; the failure of the naive integration at `t → 0` is
  exactly what the factor-`16` anchor below repairs.

  Mathematically both bounds are consequences of `hHess` + `hgrad` + `hsmC` + `hdiam` (with
  `4 ε₁ π < c`, `c ≤ 1/4`): the Hessian bound `|Hess (fcos q) + (fcos q) · g| ≤ ε₁` on
  `{fcos q > -1 + c}` says that the metric is the round unit sphere up to `ε₁` at *every* scale up to
  `L`, and both the non-vanishing of `Z` and the factor-`16` comparison with `sin t` follow from it.
  (For `ε₁ = 0` and the round unit sphere both statements are equalities: `Z t = sin t · w`.)

Both statements are stated for the *exact* field `Z` used downstream, with the same hypotheses as
`RauchSphereMapProp` (so that they can be instantiated by `intro`-ing the same argument list).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.GeoCrux

/-- **The ray from `q` does not stop being minimising before `π - arccos (1-c)`.**  Equivalently: the
exponential map at `q` is injective on the ball of radius `π - arccos (1-c)`. -/
abbrev CutInjectProp : Prop :=
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
    ∀ q : M, Submission.InjRadius.InjAtLeast hmet q
      (Real.pi - Real.arccos (1 - c))

/-- **The modulus of the radial variation field is close to the round-sphere model `sin t`.**  For
orthonormal `v, w ∈ T_qM` and `0 < t < π - arccos (1-c)`, the modulus of the variation field
`Z t = curveVelocity (fun r => GExp q (t • (v + r • w))) 0` of the family of rays out of `q` satisfies

`sin t / 2 ≤ ‖Z t‖`   and   `‖Z t‖ ≤ sin t + 3 * (ε₁ * (1 + log(2/t)^2) + t^2) * t`.

On the round unit sphere `Z t = sin t • w`, so `‖Z t‖ = sin t` and both inequalities hold with room to
spare.

**The shape of the additive error term.**  The *lower* bound is only there to guarantee that `Z` does
not vanish (so that `log ‖Z t‖` and the Sturm/Grönwall comparison are available on `(0,ρ)`; it is a
consequence of the same two-sided shape-operator bound as the upper one).  The *upper* bound is the
"anchor" of the comparison: `(log ‖Z t‖)' = Hess (rdist q) (γ t) (Z t, Z t)/‖Z t‖²`, whose *round*
part integrates to `log (sin t / t)`, and the *error* part is bounded in absolute value by
`ε₁/sin t` (`Work.Diff.C.rhess_rdist_bound_of_hHess`) at *each* scale `t`.

The error term `3 (ε₁ (1 + log(2/t)²) + t²) t` is exactly what a naive integration of that bound
gives once one uses that the *weighted average* of the curvature over the scales `(0,t]` — which is
what the shape operator at scale `t` measures — is itself bounded by `1 + O(ε₁/t²)` at every scale,
so that the divergent-looking integral `∫₀^t (S - cot)` is only allowed a `log`-sized accumulation;
the `t²` term is the contribution of the (unbounded, but finite) curvature at the base point, which
the constraint at the scaling `t` bounds by `O(ε₁)/(t sin t)`.  Both are harmless for the application:
propagating the anchor from `δ := √(c/4)` up to `ρ` costs a factor
`sin ρ / sin δ ≈ ρ/δ`, so the error contributed to the final bound is
`≈ 6 ρ (ε₁ (1 + log(2/δ)²) + c/4)`, i.e. `O(c log(1/c)² + ρ ε₁ log(1/c)²)`, which is
`≤ 40 (√c + ε₁ π)` for every `c ≤ 1/4` (using `4 ε₁ π < c`). -/
abbrev RadialModulusProp : Prop :=
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
    ∀ (q : M) (v w : TangentSpace I q),
      Inner.inner ℝ v v = 1 → Inner.inner ℝ w w = 1 → Inner.inner ℝ v w = 0 →
      ∀ t ∈ Set.Ioc (0 : ℝ) (Real.pi - Real.arccos (1 - c)),
        Real.sin t / 2 ≤ ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
            (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + r • w))) 0‖ ∧
        ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
            (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + r • w))) 0‖
          ≤ Real.sin t
            + 3 * (ε₁ * (1 + (Real.log (2 / t)) ^ 2) + t ^ 2) * t

end Work.Diff.C.GeoCrux
