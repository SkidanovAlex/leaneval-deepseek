import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.init_data
import Submission.Work.Diff.C.geoCrux.FarDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two geometric inputs of the *bad branch* of `Work.Diff.C.gram_bad_case`

`Work.Diff.C.gram_bad_case` needs, for the bad index `i = Fin.succ k` (a `Fin.succ` index whose
model `β_k sin σ` dips below `-1 + 3c` somewhere on `[0,s]`), the following facts about the ray
`γ τ = GExp p (τ • u)`, for `τ ∈ [0,s]` (so that `rdist p (γ τ) = τ`):

* (G-a) a *clamp* time of the bad index sits at distance `π/2` from the base point:
  `f_{i}(γ τ) ≤ -1 + 2c → |cos τ| ≤ 60 (√c + ε₁π)`;
* (G-b) on the far part of the ray (`τ ≥ π - arccos (1-2c)`, i.e. `cos τ ≤ -1 + 2c`, the part where
  the *index* `0` is clamped) the value of the bad index is small:
  `|f_{i}(γ τ)| ≤ 60 (√c + ε₁π)`;
* (G-c) the model comparison holds on the *whole* ray:
  `|f_{i}(γ τ) - β_k sin τ| ≤ 60 (√c + ε₁π)`.

These are the statements that the dip analysis produces: (G-c) is the prefix comparison
(`gp_ode_compare`) before the first dip, the trivial comparison inside the dip (both sides are
`≈ -1`), and a *restarted* comparison at the dip exit; (G-a) and (G-b) follow from (G-c) together
with the *length* of the dip, i.e. from the far-ball diameter bound, which is the `SphereSizeProp`
(Rauch) input of `geoCrux/FarDefs.lean`.

The far-ball diameter bound is isolated here as its own `Prop` (`FarBallDiamProp`) so that it can be
delegated and proved independently; `BadIndexModelProp` takes it as an explicit hypothesis (stated
inline, so that no universe-frozen local `Prop` has to be instantiated).

Both `Prop`s are packaged as closed `abbrev`s in the style of `Submission.Work.Diff.C.GeoCrux.Defs`:
the delegation harness elaborates the submitted statement in a file with only the `depends_on`
imports and no `open` commands, and in that bare context the Riemannian-bundle binders of a direct
statement do not elaborate.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.GeoCrux

/-- **The far ball of a point at distance `π/2` from `p` has small diameter.**  With
`q = qpt hmet p e (Fin.succ k)` (the point at distance `π/2` from `p` in the direction `e k`), any
two points at distance `≥ π - arccos (1-c)` from `q` are within `50 (√c + ε₁ π)` of each other.

This is the quantitative form of "the metric is the round unit sphere up to `ε₁`": the far ball
`{rdist q · ≥ π - arccos (1-c)}` is (in the round case) the ball of radius `arccos (1-c)` around the
antipode of `q`, of diameter `2 arccos (1-c) ≤ 2.9 √c`.

Route: `SphereSizeProp` (`geoCrux/FarDefs.lean`) bounds the size of every geodesic sphere
`{rdist q · = ρ}` by `π sin ρ + o(1)`; two points at distance `≥ π - δ` from `q` lie at distance
`≥ ρ` for a suitable `ρ ≤ π - δ` on the corresponding minimising rays from `q`, and the sphere-size
bound is monotone in `ρ` along those rays (`far_ball_excess`/`dip_far_ball` in the workspace). -/
abbrev FarBallDiamProp : Prop :=
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
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    (hdiam : ∀ y : M, rdist (I := I) (M := M) p y ≤ Real.pi)
    (k : Fin (Module.finrank ℝ E)),
    ∀ z z' : M,
      Real.pi - Real.arccos (1 - c)
          ≤ rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z →
      Real.pi - Real.arccos (1 - c)
          ≤ rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z' →
      rdist (I := I) (M := M) z z' ≤ 50 * (Real.sqrt c + ε₁ * Real.pi)

/-- **The bad index follows its model, and its clamps are at the equator.**  Let
`β_k = ⟪e k, u⟫`, `i = Fin.succ k`, `γ τ = GExp p (τ • u)`, and assume that the *model*
`τ ↦ β_k sin τ` dips below `-1 + 3c` somewhere on `[0,s]` (`hbad`).  Then, given the far-ball
diameter bound (`hfar`), for every `τ ∈ [0,s]`:

* the model comparison `|f_i(γ τ) - β_k sin τ| ≤ 60 (√c + ε₁π)`;
* a clamp time of `i` is at the equator: `f_i(γ τ) ≤ -1 + 2c → |cos τ| ≤ 60 (√c + ε₁π)`;
* the value of `i` on the far part of the ray is small:
  `π - arccos (1-2c) ≤ τ → |f_i(γ τ)| ≤ 60 (√c + ε₁π)`.

The proof is: the prefix comparison (`gp_ode_compare`) on the part of the ray before the *first* dip
time `a₁` (which gives `a₁ ∈ π/2 ± 2.4 √(c+ε₁π)`), the fact that all dip times lie within the far
ball of `q_k` whose diameter is bounded by `hfar` (so the dip is short and near `π/2`), and a
restarted comparison at the last dip time (whose initial derivative is bounded by `√(2c-c²)` by the
eikonal identity at the boundary of the region). -/
abbrev BadIndexModelProp : Prop :=
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
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    (hdiam : ∀ y : M, rdist (I := I) (M := M) p y ≤ Real.pi)
    (hfar : ∀ (k : Fin (Module.finrank ℝ E)) (z z' : M),
      Real.pi - Real.arccos (1 - c)
          ≤ rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z →
      Real.pi - Real.arccos (1 - c)
          ≤ rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z' →
      rdist (I := I) (M := M) z z' ≤ 50 * (Real.sqrt c + ε₁ * Real.pi))
    {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hsπ : s ≤ Real.pi)
    (hray : ∀ τ ∈ Set.Icc (0 : ℝ) s,
      rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) = τ)
    (k : Fin (Module.finrank ℝ E))
    (hbad : ∃ σ : ℝ, σ ∈ Set.Icc (0 : ℝ) s
      ∧ Inner.inner ℝ (e k) u * Real.sin σ < -1 + 3 * c),
    (∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) s →
        fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) ≤ -1 + 2 * c →
        |Real.cos τ| ≤ 60 * (Real.sqrt c + ε₁ * Real.pi))
    ∧ (∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) s → Real.pi - Real.arccos (1 - 2 * c) ≤ τ →
        |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))|
          ≤ 60 * (Real.sqrt c + ε₁ * Real.pi))
    ∧ (∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) s →
        |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
            - Inner.inner ℝ (e k) u * Real.sin τ|
          ≤ 60 * (Real.sqrt c + ε₁ * Real.pi))

end Work.Diff.C.GeoCrux
