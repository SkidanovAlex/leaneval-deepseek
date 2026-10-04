import Mathlib
import Submission.Work.Diff.C.geoCrux.HingeDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The "far-ball diameter" vocabulary for the hard half of the hinge bound

`Work.Diff.C.geoCrux.FarBallDiameterProp` is the one geometric input that the proof of
`Work.Diff.C.GeoCrux.HingeCosHardProp` still needs (see `geoCrux/hinge_cos_hard.lean`, whose status
block records the complete reduction to it).

In the setting of the hinge bound (a metric whose `fcos q = cos ∘ d(q,·)` satisfies, for **every**
centre `q`, the round-sphere Hessian estimate `|Hess fcos q + fcos q · g| ≤ ε₁ g` on the region
`{fcos q > -1 + c}`, the eikonal identity `|∇fcos q|² = 1 - (fcos q)²` there, smoothness on the
closed region and `diam ≤ π`), the *far ball* of a centre `y`, i.e. the set

`{z : rdist y z ≥ π - arccos (1 - c)}`   (`= {z : fcos y z ≤ -1 + c}`),

is small: its diameter is at most `2 sin (arccos (1-c)) + O(ε₁ log (1/ε₁))`, because on the round
unit sphere it is the ball of radius `δ = arccos (1-c)` around the antipode of `y`, of diameter
`2 sin δ ≤ 2 √(2c)`.  The statement below asks for the constant `(73/10) √(c + ε₁ π)`: a prover of this very statement
reported that the honest route (radial projection of the two far points onto the geodesic sphere of
radius `π - arccos (1-c)`, plus the ambient size `π sin (π - arccos (1-c)) ≈ 4.4 √c` of that sphere)
gives `2 arccos (1-c) + π sin (π - arccos (1-c)) + O(ε₁π) ≈ 7.27 √c + O(ε₁π)`, i.e. `7` was too
sharp while `7.3` is reachable; the phase bookkeeping of `hinge_cos_hard` tolerates anything `≤ 7.3`
(its arithmetic is `(8/5 + 73/10)²/2 = 39.6 ≤ 40`).

## ⚠ Diagnosis for the prover: what does *not* work, and why

This note is written so that no one re-runs a route that has already been shown to be blind to this
statement.

1. **The "sum of two distance functions" (excess / PSD) technique does NOT give it.**
   That technique (`Work.Diff.C.far_ball_excess`) uses: along a minimising geodesic `η` from `u` to
   `v` of length `L`, the function `F = rdist u + rdist v` is `≥ L` with equality on `η`, hence
   `Hess F ≥ 0` on `η`; combined with the two Hessian comparisons this yields
   `cot t + cot (L-t) ≥ -ε₁ (1/sin t + 1/sin (L-t))`, i.e. `sin L ≥ -2ε₁` (the arithmetic kernel is
   proved in `Work.Diff.C.geoCrux`: `cot_add_cot`, `sin_L_ge_of_cot_sum`, `sin_L_ge_neg_two_mul`).
   But `sin L ≥ -2ε₁` is **vacuous for `L ≤ π`** (`sin ≥ 0` there) and can only produce bounds
   *near* `π`: it says "a distance that is already `≥ π - δ` is `≤ π + 2ε₁`".  It is structurally
   blind to distances below `π - δ` — it cannot bound the *diameter* of a set of size `~√c`, which
   is what is needed here.
2. **The classical Rauch / Jacobi-modulus route is blocked upstream.**  The sharp modulus engine
   `Work.Diff.C.modulus_le_sin_add_sqrt` needs the *quantitative* asymptotics `|u t - a t| ≤ C t³`
   (explicit `C ≲ 40 a`) of the modulus of the Jacobi field with `J(0) = 0` along the ray from `y`.
   That needs a *pointwise* lower bound for the curvature at the centre `y`: the hypotheses only
   bound the *shape operator* of the geodesic spheres, and a pointwise curvature bound does not
   follow from them with any constant (this is the recorded finding that
   `Work.Diff.C.pinch_from_hess` is **false** as stated).  With the crude `8√ε₁(a+C)` error the
   resulting sphere size is `≈ 6.7 √c`, which does not fit the constant `7` of this statement but is
   only a factor `~1.3` away — so a route that improves the *asymptotic* input, or that uses the
   hypotheses at **all** centres (e.g. by controlling the curvature at `y` through the Hessian
   comparisons centred at points near `y`), is what is needed.
3. **The hinge comparison along the whole leg is unavailable.**  The geodesic between two points of
   `∂(far ball)` passes through the far ball itself, where `fcos y < -1 + c` and hence where
   `hHess` (the only differential hypothesis about the centre `y`) simply does not apply.
   A replacement centre (`x`, or a midpoint) fails at the centre of the interval for the same reason.

## What a proof must produce

Anything of the shape `rdist z z' ≤ K √(c + ε₁π)` with `K ≤ 73/10` for all `z, z'` with
`rdist y z, rdist y z' ≥ π - arccos (1-c)`.  In particular the *sharp* form
`2 sin (arccos (1-c)) + C ε₁ log (1/ε₁)` would do (it is `≤ 2.83 √c + o(√c)`).

Nothing here is proved; the file only fixes the statement so that it can be delegated.
-/
set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.geoCrux

/-- **The far ball of a centre `y` has diameter at most `7 √(c + ε₁ π)`.**

See the module docstring: this is the quantitative smallness of the set
`{z : rdist y z ≥ π - arccos (1-c)}` under the C-area hypotheses (`hHess`, `hgrad`, `hsmC`,
`hcont`, `hdiam`). -/
abbrev FarBallDiameterProp : Prop :=
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
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    (y : M),
    ∀ z z' : M,
      Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) y z →
      Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) y z' →
      rdist (I := I) (M := M) z z' ≤ (73 / 10) * Real.sqrt (c + ε₁ * Real.pi)

/-- **The "first entry" bound of the hard case of the hinge theorem.**

If the ray `σ ↦ GExp x (σ • u)` (with `u` a unit vector, `0 ≤ σ ≤ s ≤ π`) stays in the *open* region
`{fcos y > -1 + c}` on `[0,σ)` and reaches the closed region at `σ` (`fcos y (γ σ) ≤ -1 + c`), then

  `rdist x y + σ ≤ π + arccos (1 - c - ε₁π)`,

i.e. `a + σ - π ≤ arccos (1 - c - ε₁π)`; this is the `hentry` input of
`Work.Diff.C.geoCrux.hinge_hard_assembly`.

Route: `ray_cos_compare` on `[0,τ]` for each `τ < σ` (the Hessian bound `hHess y` is available there
because the ray is in the open region) gives
`cos (a+τ) ≤ fcos y (γ τ) + ε₁ τ`, since `⟪∇(fcos y)(x), u⟫ ≥ -sin a` follows from the modulus bound
`Work.Diff.C.eik_abs_mvfderiv_fcos_le`; letting `τ ↑ σ` (using `hcont y` and the smoothness of the
ray, `Submission.ConjEnergy.contMDiff_GExp_smul`) gives `cos (a+σ) ≤ -1 + c + ε₁ σ`; finally
`a + σ ≤ 2π` (from `hdiam`) and the monotonicity of `arccos` on `[π - arccos(1-c-ε₁σ), π + …]`
give the claim. -/
abbrev EntryBoundProp : Prop :=
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
    {c ε₁ : ℝ} (hc : 0 < c) (hε₁ : 0 ≤ ε₁) (hnum : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    (x y : M) (u : TangentSpace I x) (s σ : ℝ)
    (hu : Inner.inner ℝ u u = 1) (hs0 : 0 ≤ s) (hsπ : s ≤ Real.pi)
    (hσ0 : 0 ≤ σ) (hσs : σ ≤ s)
    (hgood : ∀ τ ∈ Set.Ico (0 : ℝ) σ,
      -1 + c < fcos (I := I) (M := M) y
        (Submission.GlobalExp.GExp (cov := cov) hmet x (τ • u)))
    (hσin : fcos (I := I) (M := M) y (Submission.GlobalExp.GExp (cov := cov) hmet x (σ • u))
      ≤ -1 + c),
    rdist (I := I) (M := M) x y + σ ≤ Real.pi + Real.arccos (1 - c - ε₁ * Real.pi)

/-- **The injectivity-radius input of the hard case.**

Under the C-area hypotheses, the exponential map at every point `x` is injective on the *open* ball
of radius `π - arccos (1-c)` in `TₓM`.

This is the hypothesis that converts the far-ball diameter into the *passage* bound
`Work.Diff.C.geoCrux.passage_le_of_far_ball_diameter`: by
`Submission.GExpRay2.edist_GExp_eq_norm_of_le_of_injAtLeast`, the ray `γ[σ₁,s]` is minimising as soon
as `s - σ₁ ≤ π - arccos (1-c)`, so its length is the distance of its endpoints, which the far-ball
diameter bounds.

Route: `hsmC` says `fcos x = cos ∘ rdist x` is smooth on the *closed* region
`{fcos x ≥ -1+c}` = `{rdist x ≤ π - arccos (1-c)}`; hence `rdist x` is smooth there (compose with
`arccos` away from `±1`), so no point of that region is a cut point of `x`, and at a non-cut point
the minimising geodesic from `x` is unique: two geodesics from `x` of length `< π - arccos (1-c)`
ending at the same point would give two minimising geodesics and hence a non-smooth point of
`rdist x` at distance `< π - arccos (1-c)`, contradicting `hsmC`.  The relevant cut-point material
is in `Submission.CutPoint` / `Submission.CutTime` / `Submission.InjRadius`. -/
abbrev InjectivityProp : Prop :=
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
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    (x : M),
    Submission.InjRadius.InjAtLeast hmet x (Real.pi - Real.arccos (1 - c))

end Work.Diff.C.geoCrux
