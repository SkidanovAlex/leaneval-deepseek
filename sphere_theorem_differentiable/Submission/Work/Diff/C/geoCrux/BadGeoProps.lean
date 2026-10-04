import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.dip_model_through
import Submission.Work.Diff.C.ode_compare_halfopen
import Submission.Geodesic
import Submission.GlobalExp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two analytic inputs of `Work.Diff.C.GeoCrux.BadIndexModelProp`

`Submission/Work/Diff/C/geoCrux/BadGeoDefs.lean` isolates the bad-index model comparison
(`BadIndexModelProp`) of the bad branch of `Work.Diff.C.gram_bad_case`.  Proving it needs two
independent analytic facts about the minimising ray `γ σ = GExp p (σ • u)` from `p` in the unit
direction `u`, with `q = qpt hmet p e (Fin.succ k)` (so `rdist q p = π/2`):

* `RestartCompareProp` — the **Sturm comparison restarted at an interior time `b`**, in the
  *half-open* form: the forcing bound `|Hess f + f·g| ≤ ε` is required only on `(b, τ]`, so that the
  comparison applies when the function `f` is clamped (`f = -1+c` exactly) at the left endpoint.
  Both the value and the derivative comparison are concluded.
  (Template: the proved `Work.Diff.C.gp_ode_compare` / `Work.Diff.C.gp_ode_compare_deriv`, which are
  the same statement anchored at `b = 0` with the forcing on `[0, τ]`; the solver of
  `ode_compare_halfopen` is the proved scalar engine.)

* `DipGeoProp` — the **geometry of the dip** (the set `{σ : cos (rdist q (γ σ)) ≤ -1+c}`):
  every point of the *c*-dip is at distance `≥ π - arccos (1-c)` from `q` (so the far-ball
  hypothesis `hfar` applies to any two of them), still at distance `≤ π + arccos (1-c)` (so the
  *sine* of its distance to `q` is small), the dip is short (`|σ - σ'| ≤ 50(√c + ε₁π)` for two dip
  times, hence `|σ - π/2| ≤ 50(√c + ε₁π) + 2.6√c` using the location of the first dip time), and
  every point of the *2c*-dip (`cos ≤ -1+2c`) is also at distance `≥ π - arccos (1-c)`.

These `Prop`s are packaged as closed `abbrev`s (in the style of `BadGeoDefs.lean`) because the
delegation harness elaborates a submitted statement in a file with only the `depends_on` imports and
no `open` commands; in that bare context the Riemannian-bundle binders of a direct statement do not
elaborate.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.GeoCrux

/-- **The Sturm comparison for `f` along the ray from `p`, restarted at the interior time `b`.**

`γ σ = GExp p (σ • u)` with `⟪u,u⟫ = 1`, `0 ≤ b ≤ τ`.  If `f` is `C^∞` at every `γ θ`,
`θ ∈ [b,τ]`, and the Hessian bound `|rhess f (γθ) V V + f (γθ) ⟪V,V⟫| ≤ ε ⟪V,V⟫` holds on the
*half-open* interval `θ ∈ (b,τ]` (so nothing is required at the left endpoint `b`), then along the
ray `f` is within `ε(τ-b)` of the solution of `y'' + y = 0` with the data `(f(γb), ⟪∇f(γb), γ'b⟫)`
at `b`, both for the values and for the derivatives. -/
abbrev RestartCompareProp : Prop :=
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
    {p : M} {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1)
    {f : M → ℝ} {ε b τ : ℝ} (hε : 0 ≤ ε) (hb : 0 ≤ b) (hbτ : b ≤ τ)
    (hsm : ∀ θ ∈ Set.Icc b τ,
      CMDiffAt ∞ f (Submission.GlobalExp.GExp (cov := cov) hmet p (θ • u)))
    (hHess : ∀ θ ∈ Set.Ioc b τ,
      ∀ V : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (θ • u)),
        |rhess cov f (Submission.GlobalExp.GExp (cov := cov) hmet p (θ • u)) V V
          + f (Submission.GlobalExp.GExp (cov := cov) hmet p (θ • u)) * Inner.inner ℝ V V|
        ≤ ε * Inner.inner ℝ V V) ,
    |f (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
      - (f (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u)) * Real.cos (τ - b)
        + Inner.inner ℝ (rgrad (I := I) (M := M) f
              (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u)))
            (Submission.Geodesic.curveVelocity (I := I)
              (fun σ : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) b)
          * Real.sin (τ - b))| ≤ ε * (τ - b)
    ∧ |Inner.inner ℝ (rgrad (I := I) (M := M) f
            (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)))
          (Submission.Geodesic.curveVelocity (I := I)
            (fun σ : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) τ)
        - (Inner.inner ℝ (rgrad (I := I) (M := M) f
              (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u)))
            (Submission.Geodesic.curveVelocity (I := I)
              (fun σ : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) b)
            * Real.cos (τ - b)
          - f (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u)) * Real.sin (τ - b))|
        ≤ ε * (τ - b)

/-- **The geometry of the dip of the ray in the antipodal ball of `q`.**

`γ σ = GExp p (σ • u)` is a minimising ray from `p` in the unit direction `u` on `[0,s]`
(`rdist p (γ σ) = σ`, `s ≤ π`), `rdist q p = π/2`, the far ball of `q` has diameter
`≤ 50 (√c + ε₁π)` (`hfar`), and `a` is a `c`-dip time located by `|a - π/2| ≤ 2.6 √c`.  Then:

* every `c`-dip time (`cos (rdist q (γ σ)) ≤ -1+c`) is at distance `≥ π - arccos (1-c)` from `q`,
  hence (with the same for `a`) two of them are within `50 (√c + ε₁π)`,
  so `|σ - σ'| ≤ 50 (√c + ε₁π)` (the sub-arc of a minimising ray realises its length);
* every `c`-dip time satisfies `|σ - π/2| ≤ min (50 (√c + ε₁π) + 2.6√c) (π/2)`;
* every `c`-dip time is also at distance `≤ π + arccos (1-c)` from `q` (so the *sine* of its
  distance to `q` is at most `sin (arccos (1-c)) = √(2c-c²)`).

(Warning: the *2c*-dip is strictly **larger** than the `c`-dip, so it is **not** contained in the far
ball of `q`: `{cos ≤ -1+2c} = {rdist q · ≥ π - arccos (1-2c)}` and `arccos (1-2c) > arccos (1-c)`.
No such claim is made here.) -/
abbrev DipGeoProp : Prop :=
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
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    {p q : M} (hqp : rdist (I := I) (M := M) q p = Real.pi / 2)
    {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hsπ : s ≤ Real.pi)
    (hray : ∀ τ ∈ Set.Icc (0 : ℝ) s,
      rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) = τ)
    (hfar : ∀ z z' : M,
      Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) q z →
      Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) q z' →
      rdist (I := I) (M := M) z z' ≤ 50 * (Real.sqrt c + ε₁ * Real.pi))
    {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) s)
    (ha_cos : Real.cos (rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))) = -1 + c)
    (ha_phase : |a - Real.pi / 2| ≤ 2.6 * Real.sqrt c) ,
    (∀ {σ : ℝ}, σ ∈ Set.Icc (0 : ℝ) s →
      Real.cos (rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) ≤ -1 + c →
      Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)))
    ∧ (∀ {σ : ℝ}, σ ∈ Set.Icc (0 : ℝ) s →
      Real.cos (rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) ≤ -1 + c →
      rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
        ≤ Real.pi + Real.arccos (1 - c))
    ∧ (∀ {σ : ℝ}, σ ∈ Set.Icc (0 : ℝ) s →
      Real.cos (rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) ≤ -1 + c →
      |σ - Real.pi / 2| ≤ min (50 * (Real.sqrt c + ε₁ * Real.pi) + 2.6 * Real.sqrt c)
        (Real.pi / 2))
    ∧ (∀ {σ σ' : ℝ}, σ ∈ Set.Icc (0 : ℝ) s → σ' ∈ Set.Icc (0 : ℝ) s →
      Real.cos (rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) ≤ -1 + c →
      Real.cos (rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ' • u))) ≤ -1 + c →
      |σ - σ'| ≤ 50 * (Real.sqrt c + ε₁ * Real.pi))
/-- **The "annulus" phase bound (pure real analysis).**

`Fb = -1+c` is the value of the ray function at the last dip time `b`, `Fp` its derivative there
(`|Fp| ≤ √(2c-c²)` by the eikonal identity at a clamp point), `z = τ - b ∈ [0,π]`, and the restart
comparison gives `|Fτ - (Fb cos z + Fp sin z)| ≤ ε₁ z`.  If in addition the value at `τ` is still
within `2c` of the minimum (`-1+c < Fτ ≤ -1+2c`), then `z ≤ 3.5 √c`.

This is the "annulus case" of the clamp-phase bound: a clamp time lying only just outside the
`c`-dip (but still within `2c` of the minimum `-1`) is within `3.5√c` of the last dip time, hence
within `50(√c+ε₁π) + 2.6√c + 3.5√c ≤ 60(√c+ε₁π)` of `π/2`.

Proof sketch: `z ≥ π/2` is impossible (there `Fb cos z + Fp sin z ≥ -√(2c-c²)`, so
`Fτ ≥ -√(2c-c²) - ε₁π`, contradicting `Fτ ≤ -1+2c` for `c ≤ 1/96`), and for `z ∈ [0,π/2]` the two
inequalities `Fτ > -1+c` and `Fτ ≤ -1+2c` give
`ℓ(z) := (1-c)(1-cos z) - √(2c-c²) sin z < ε₁ z ≤ (c/4)·z`; `ℓ` is convex with `ℓ(0) = 0`,
`ℓ'(0) = -√(2c-c²) < 0`, and `ℓ(z) ≥ 0.45 z² - 1.42√c z` for `z ≤ 1`, while `ℓ(z) > ε₁ z` for
`z ∈ [1,π/2]` (numerically `ℓ(1) ≥ 0.33 > ε₁π/2`); so `z ≤ 3.2√c`. -/
abbrev AnnulusPhaseProp : Prop :=
  ∀ {c ε₁ Fb Fp Fτ z : ℝ}, 0 < c → c ≤ 1 / 96 → 0 ≤ ε₁ → 4 * ε₁ * Real.pi < c →
    0 ≤ z → z ≤ Real.pi → Fb = -1 + c →
    |Fp| ≤ Real.sqrt (2 * c - c * c) →
    |Fτ - (Fb * Real.cos z + Fp * Real.sin z)| ≤ ε₁ * z →
    -1 + c < Fτ → Fτ ≤ -1 + 2 * c → z ≤ 3.5 * Real.sqrt c

/-- **The "good region" value arithmetic (pure real analysis).**

In the situation of `RestartCompareProp` anchored at the last dip time `b ≥ π/2` (`γ' = b - π/2 ≥ 0`,
`|γ'| ≤ 50(√c+ε₁π) + 2.6√c`, `|γ'| ≤ π/2`), with `z = τ - b ∈ [0, π/2 - γ']` and the anchor
discrepancies `A = F b - m b`, `B = F'(b) - m'(b)` bounded by
`|A| ≤ 2c + (1-cos γ')`, `|B| ≤ √(2c-c²) + sin γ'` (`m` the trigonometric model), one has
`|A cos z + B sin z| + ε₁π + 2√c ≤ 60(√c + ε₁π)`. -/
abbrev GoodValueArithProp : Prop :=
  ∀ {c ε₁ A B γ' z L : ℝ}, 0 < c → c ≤ 1 / 96 → 0 ≤ ε₁ → 4 * ε₁ * Real.pi < c →
    L = Real.sqrt c + ε₁ * Real.pi →
    0 ≤ γ' → γ' ≤ min (50 * (Real.sqrt c + ε₁ * Real.pi) + 2.6 * Real.sqrt c) (Real.pi / 2) →
    0 ≤ z → z ≤ Real.pi / 2 - γ' →
    |A| ≤ 2 * c + (1 - Real.cos γ') →
    |B| ≤ Real.sqrt (2 * c - c * c) + Real.sin γ' →
    min (|A| + |B| * Real.cos γ') (Real.sqrt (A ^ 2 + B ^ 2)) + ε₁ * Real.pi + 2 * Real.sqrt c
      ≤ 60 * L

/-- **The phase of the *first* dip time (pure real analysis).**

`β ≤ -(1-3c)` (the model dips below `-1+3c` somewhere), and at the first dip time `a ∈ [0,π]` the
model comparison `|(-1+c) - β sin a| ≤ ε₁ a` holds (from `dip_first_compare`).  Then
`|a - π/2| ≤ 2.6 √c`: indeed `1 - sin a ≤ 1 - |β| sin a = |m a + 1| ≤ c + ε₁π ≤ 1.25c`, so
`|cos a| ≤ √(2.5c)` and `|a - π/2| ≤ (π/2)|cos a| ≤ 2.49√c`. -/
abbrev FirstDipPhaseProp : Prop :=
  ∀ {β a c ε₁ : ℝ}, 0 < c → c ≤ 1 / 96 → 0 ≤ ε₁ → 4 * ε₁ * Real.pi < c →
    0 ≤ a → a ≤ Real.pi → β ≤ -(1 - 3 * c) → -1 ≤ β →
    |(-1 + c) - β * Real.sin a| ≤ ε₁ * a → |a - Real.pi / 2| ≤ 2.6 * Real.sqrt c

end Work.Diff.C.GeoCrux
