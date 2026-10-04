import Mathlib
import Submission.Work.Diff.C.geoCrux.RadialBase
import Submission.Work.Diff.C.geoCrux.RauchInputDefs
import Submission.JacobiGlobal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The geometric core pieces of the radial-modulus bound, as closed `Prop`s

This module collects, as closed `abbrev`s, the statements of the three geometric inputs that the
radial-modulus bound (`Work.Diff.C.geoCrux.radial_modulus_sharp`, and the equivalent
`Work.Diff.C.RadialBound.radial_modulus_bound`) needs, so that they can be delegated to colleagues
(the delegation harness elaborates a submitted statement in a file that imports only the
`depends_on` modules and has no `open` commands, so the statements have to be closed `Prop`s here).

* `TwoCentreCoreProp` — the **two-centre inequality** (the geometric core of the modulus estimate):
  it is the body of `Work.Diff.C.geoCrux.RadialTwoCentreProp` but with the *injectivity-radius*
  hypothesis `hcut : ∀ q, InjAtLeast q (π - arccos (1-c))` (which, unlike a *global* diameter bound
  `∀ x y, rdist x y ≤ π`, is available in the C-area setting from `hsmC`/`hgrad` alone: the region
  `{fcos q ≥ -1+c}` contains the closed ball of radius `π - arccos (1-c)` around `q`, and `rdist q`
  is smooth with unit gradient there, so no point of that closed ball is a cut point of `q`).  The
  strictness `τ < π - arccos (1-c)` (rather than `≤`) is what makes the shape-operator hypothesis
  `hHess (γ τ)` applicable at both `q` and `γ σ` (it needs `fcos (γ τ) > -1 + c`, i.e. `cos τ > -1+c`
  and `cos (τ-σ) > -1+c`).

* `InjRadiusCoreProp` — the **injectivity radius** `InjAtLeast hmet q (π - arccos (1-c))` for every
  `q`, from the C-area hypotheses *without* a global diameter bound.  This is the C-area version of
  `Work.Diff.C.geoCrux.InjectivityProp`, with its hypothesis `hdiam : ∀ x y, rdist x y ≤ π` removed
  (the existing proof `Submission.Work.Diff.C.geoCrux.injectivity_radius` passes `hdiam` through its
  internal lemmas; the local statements it needs are the `hdiam`-free ones, cf.
  `Work.Diff.C.fbcap_rdist_smooth`).

* `JacobiUniqProp` — **uniqueness of Jacobi fields** with prescribed value and covariant derivative at
  one time (the statement of `Submission.Work.Diff.C.isJacobiAt_eq_of_data`, restated as a closed
  `Prop` and hence delegable).  It is what identifies an arbitrary Jacobi field `Z` along a ray with
  the radial variation field of the family of rays out of the base point, i.e. what converts the
  modulus bound for the variation fields into the modulus bound for all Jacobi fields
  (`Work.Diff.C.RadialBound.radial_modulus_bound`).

Everything here is a *statement*; nothing is proved in this module.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.geoCrux.Port

/-- **The two-centre inequality** (geometric core of the modulus estimate), with the
injectivity-radius hypothesis replacing the global diameter bound of `RadialTwoCentreProp`.

For `0 < σ < τ ≤ 2σ`, `τ < π - arccos (1-c)`, with `κ := twoK σ τ = cot σ + cot(τ-σ)`,
`λ := twoL σ τ = cot σ - cot τ`, `δ := twoD ε₁ σ τ = ε₁(1/sin σ + 1/sin(τ-σ))`,
`η := twoE ε₁ σ τ = ε₁(1/sin σ + 1/sin τ)`, there is `N ≥ 0` such that, writing
`Z_ξ(s) := curveVelocity (fun r ↦ GExp q (s • (v + r • ξ))) 0` for `ξ ⊥ v`:

* `‖Z_ξ(σ)‖ ≤ N‖ξ‖` for all `ξ ⊥ v`;
* `(κ-δ)(λ-η)N² ≤ 1`;
* for every unit `w ⊥ v`: `1 ≤ (κ+δ)(λ y_w² + η N y_w)` and `1 ≥ (κ-δ)(λ y_w² - η N y_w)`, where
  `y_w := ‖Z_w(σ)‖`.

See the module docstring of `Submission.Work.Diff.C.geoCrux.radial_modulus` for the mathematics (the
Wronskian of the forward variation field with the field vanishing at `γ τ`) and
`Submission.Work.Diff.C.geoCrux.radial_modulus`'s `modulus_of_twoCentre` /
`modulus_two_sided` for the (proved) extraction of the modulus bounds from these three
inequalities. -/
abbrev TwoCentreCoreProp : Prop :=
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
    (hcut : ∀ q : M, Submission.InjRadius.InjAtLeast hmet q (Real.pi - Real.arccos (1 - c)))
    (q : M) (v : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (σ τ : ℝ) (hσ : 0 < σ) (hστ : σ < τ) (hτ2 : τ ≤ 2 * σ)
    (hτ : τ < Real.pi - Real.arccos (1 - c)),
    ∃ N : ℝ, 0 ≤ N ∧
      (∀ ξ : TangentSpace I q, Inner.inner ℝ v ξ = 0 →
        ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
            (σ • (v + r • ξ))) 0‖ ≤ N * ‖ξ‖) ∧
      0 < twoK σ τ ∧ 0 < twoL σ τ ∧
      (twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ - twoE ε₁ σ τ) * N ^ 2 ≤ 1 ∧
      ∀ w : TangentSpace I q, Inner.inner ℝ v w = 0 → Inner.inner ℝ w w = 1 →
        1 ≤ (twoK σ τ + twoD ε₁ σ τ) *
              (twoL σ τ * ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
                  (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
                    (σ • (v + r • w))) 0‖ ^ 2
                + twoE ε₁ σ τ * N * ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
                  (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
                    (σ • (v + r • w))) 0‖) ∧
        1 ≥ (twoK σ τ - twoD ε₁ σ τ) *
              (twoL σ τ * ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
                  (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
                    (σ • (v + r • w))) 0‖ ^ 2
                - twoE ε₁ σ τ * N * ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
                  (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
                    (σ • (v + r • w))) 0‖)

/-- **The injectivity radius from the C-area hypotheses, without a global diameter bound.**

Under `hsmC`/`hHess`/`hcont`/`hgrad` (the metric is the round unit sphere up to `ε₁`, in the form of
the Hessian bound for `fcos q = cos ∘ rdist q` at every centre `q`), every `q` has
`InjAtLeast hmet q (π - arccos (1-c))`.

This is `Work.Diff.C.geoCrux.InjectivityProp` with its global-diameter hypothesis removed.  The
existing proof `Submission.Work.Diff.C.geoCrux.injectivity_radius` goes through the ODE/Grönwall
comparison of the radial pairing `C t = ⟪∇(rdist x)(γ t), γ'(t)⟫` along the unit ray
`γ t = GExp x (t • ξ)` (analytic core in `Submission.Work.Diff.C.geoCrux.rayCore`), and the only
place where a *global* diameter bound is used is to know `rdist x y < π` for points of the ball;
inside the ball of radius `π - arccos (1-c)` this is automatic (`π - arccos (1-c) < π`), and the local
statements needed (`rdist q` smooth with unit gradient where `cos ∘ rdist q > -1+c`, cf.
`Work.Diff.C.fbcap_rdist_smooth`) are already `hdiam`-free. -/
abbrev InjRadiusCoreProp : Prop :=
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
    (x : M),
    Submission.InjRadius.InjAtLeast hmet x (Real.pi - Real.arccos (1 - c))

/-- **Uniqueness of Jacobi fields with prescribed data at one time** (the statement of
`Submission.Work.Diff.C.isJacobiAt_eq_of_data`, as a closed `Prop`).

Two Jacobi fields along the same smooth curve (with nowhere vanishing velocity) which have the same
value and the same covariant derivative at one time are equal everywhere. -/
abbrev JacobiUniqProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) I ((⊤ : ENat) : WithTop ENat) γ)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {J : (t : ℝ) → TangentSpace I (γ t)} {Z : (t : ℝ) → TangentSpace I (γ t)}
    (hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ J t)
    (hZ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ Z t)
    {t₀ : ℝ} (hv : J t₀ = Z t₀)
    (hd : Submission.JacobiGlobal.covAlong cov J t₀
      = Submission.JacobiGlobal.covAlong cov Z t₀),
    ∀ t : ℝ, J t = Z t

/-- **The modulus bound for the radial variation fields, at every radius `ρ ≤ π - arccos (1-c)`.**

For a centre `q`, a unit `v ∈ T_qM`, a radius `0 < ρ ≤ π - arccos (1-c)` and `ξ ⊥ v`, the radial
variation field

`Z_ξ(ρ) = curveVelocity (fun r ↦ GExp q (ρ • (v + r • ξ))) 0 = d(GExp q)(ρ v)[ρ ξ]`

satisfies `‖Z_ξ(ρ)‖ ≤ (sin ρ + 25 ε₁)‖ξ‖`.  (Since `∇Z_ξ(0) = ξ`, this is the radial modulus bound;
through `Work.Diff.C.varField_eq_mfderiv` and `Work.Diff.C.geoCrux.JacobiUniqProp` it gives the
`hmod` input of `Work.Diff.C.RadialBound.GExp_radius_mfderiv_bound`, hence the size of the geodesic
sphere `S(q,ρ)` — the input of `Work.Diff.C.GeoCrux.FarBallDiamProp`.)

Route.  (1) *Anchor at every scale* `σ ≤ π/3`: the two-centre inequalities of
`Work.Diff.C.geoCrux.twoCentre_core` at `(σ, 2σ)` (available because `2σ ≤ 2π/3 < π - arccos(1-c)`
for `c ≤ 1/4`, `cos σ ≥ 1/2`) together with the proved extraction
`Work.Diff.C.geoCrux.modulus_of_twoCentre` give `sin σ/2 ≤ ‖Z_ξ(σ)‖ ≤ sin σ (1 + 7ε₁)`.
(2) *Propagation*: the shape-operator bound `Work.Diff.C.GeoCrux.ShapePolarizedProp` (proved, from
`hHess`) fed into `Work.Diff.C.jld_log_deriv_le_cot_of_shapeOp` (proved) gives
`(log ‖Z‖)' ≤ cot t + ε₁/sin t` on `(0,ρ)` — the positivity of `‖Z_ξ t‖` on that interval following
from the anchor at a small scale and the two-sided version of the same bound — so that the anchored
Sturm comparison `Work.Diff.C.GeoCrux.modulus_anchored` (proved) with `δ = π/3` gives the claim, and
the numerical endgame `(1+7ε₁)·(tan(ρ/2)/tan(π/6))^{ε₁} ≤ 1 + 25ε₁/sin ρ` (using
`4 ε₁ π < c` and `sin ρ ≥ √(c/2)/2`) finishes it. -/
abbrev VariationModulusProp : Prop :=
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
    (hcut : ∀ q : M, Submission.InjRadius.InjAtLeast hmet q (Real.pi - Real.arccos (1 - c)))
    (q : M) (v : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρπ : ρ ≤ Real.pi - Real.arccos (1 - c))
    (ξ : TangentSpace I q) (hξ : Inner.inner ℝ v ξ = 0),
    ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
        (ρ • (v + r • ξ))) 0‖
      ≤ (Real.sin ρ + 25 * ε₁) * ‖ξ‖

/-- **The `hmod` input of `Work.Diff.C.RadialBound.GExp_radius_mfderiv_bound`**: the sharp radial
modulus bound for an *arbitrary* Jacobi field `Z` along the ray `t ↦ GExp q (t • v)` with `Z 0 = 0`
whose initial covariant derivative is orthogonal to `v`, in exactly the shape in which
`GExp_radius_mfderiv_bound` consumes it (with the `hcut` derived internally from
`hsmC`/`hHess`/`hgrad`, and the general field reduced to the variation field by Jacobi uniqueness).

Provable from `Work.Diff.C.geoCrux.inj_radius_core`,
`Work.Diff.C.geoCrux.variation_modulus` (applied to the field
`Z_ξ(t) = curveVelocity (fun r ↦ GExp q (t • (v + r • ξ))) 0` with `ξ := ∇Z(0)`, which has
`∇Z_ξ(0) = ξ` by `Submission.Work.OddBound.longHomotopy.covAlong_variation_zero`) and
`Work.Diff.C.geoCrux.jacobi_uniq` (which gives `Z = Z_ξ`), together with the transports of the norm
and the inner product across the point equality `GExp q (0 • v) = q`. -/
abbrev HmodProp : Prop :=
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
    {q : M} {v : TangentSpace I q}, ‖v‖ = 1 → ∀ {ρ : ℝ}, 0 < ρ →
      ρ ≤ Real.pi - Real.arccos (1 - c) → Real.sqrt ε₁ ≤ ρ →
      ∀ {Z : (t : ℝ) → TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))},
      (∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov
        (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) Z t) →
      Z 0 = 0 → Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z 0) v = 0 →
      ‖Z ρ‖ ≤ (Real.sin ρ + 25 * ε₁)
        * ‖Submission.JacobiGlobal.covAlong cov Z 0‖

end Work.Diff.C.geoCrux.Port
