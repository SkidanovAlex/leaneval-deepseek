import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.geoCrux.RadialCutDefs
import Submission.CutTime
import Submission.InjRadius
import Submission.InjRadiusCut
import Submission.Work.Diff.C.rdist_continuous
import Submission.GExpRay2
import Submission.GExpVelocity
import Submission.GExpRayZero
import Submission.RayJacobi
import Submission.LensLoop
import Submission.Work.Diff.C.ray_minimising_near_perturbation
import Submission.Work.Diff.C.rhess_symm
import Submission.Work.Diff.GE.scal_lapl_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The three sub-statements of `Work.Diff.C.GeoCrux.RadialCutProp`

`Work.Diff.C.geoCrux.radial_cut` proves `RadialCutProp` (the cut-locus side conditions of the Rauch
input) by reduction to the three statements below, which are stated here as closed `Prop`s so that
they can be delegated in the bare context of the delegation harness (no `open` commands there).

* `RdistSmoothProp` — `rdist q` is `C^∞` inside the ball of radius `π - arccos (1-c)`: the arccos
  trick, from `hsmC` (smoothness of `cos ∘ rdist q` on `{fcos q ≥ -1+c}`) and the continuity of
  `rdist q`.
* `CutTimeGeProp` — **no cut point in the closed ball of radius `π - arccos (1-c)`**:
  `π - arccos (1-c) ≤ cutTime q ξ`.  This is the `hminW` side condition *without* strictness; once it
  is available, `Submission.InjRadiusCut.injAtLeast_of_forall_cutTime_le` gives
  `InjAtLeast hmet q (π - arccos (1-c))`, whence `Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast`
  makes all rays of norm `< π - arccos (1-c)` minimising.
* `CutTimeGtProp` — the strict form: `π - arccos (1-c) < cutTime q ξ`, needed only in the boundary
  case `ρ = π - arccos (1-c)` of `hminW`.  Route: the cut-point dichotomy (`two minimising geodesics`
  or `¬ LocallyInjectiveAtGExp`) at the cut time `τ ≤ ρ₀`; the first alternative is killed by the
  chain rule + Cauchy–Schwarz at the cut point (where `rdist q` is `C^∞` by `hsmC` *and* the eikonal
  holds), and reduces the second to the same statement via the variation family; the second, with the
  Jacobi field of `Submission.SingularConj.singular_imp_conjTime` (a variation field!), is killed by
  `Work.Diff.C.no_conjTime_le_arccos` fed with `Work.Diff.C.dmRadialOrthogonal` and
  `Work.Diff.C.dmRadialBridge` (both proved, and usable since the ray is minimising strictly below
  `τ`) and with the shape-operator bound `Work.Diff.C.rhess_rdist_bound_of_hHess`.
* `HnePartProp` — the second conjunct of `RadialCutProp` (no conjugate point along the ray), from
  `InjAtLeast hmet q ρ₀`: a vanishing variation field makes the differential of `GExp q` singular at
  `t v`, hence `GExp q` is not locally injective there, hence there are two distinct vectors `a ≠ b`
  with the same image in a *small ball* around `t v` (so `‖a‖,‖b‖ < ρ₀`), which contradicts
  `Submission.CutPoint.norm_eq_and_minimising_of_witness_pair` (both norms would equal `ρ₀`).

## Status and route (for whoever continues this)

**Proved, sorry-free, in this file** (all with `#print axioms` = `propext, Classical.choice,
Quot.sound`):

* `neg_one_add_le_fcos_of_le` — `rdist q y ≤ π - arccos (1-c) ⟹ -1 + c ≤ fcos q y` (`cos` decreasing
  on `[0,π]` plus `Real.arccos_neg`).
* **`rdist_smooth_eikonal : RdistSmoothProp`** — `rdist q` is `C^∞` inside the ball of radius
  `ρ₀ := π - arccos (1-c)` (the `arccos` trick: `rdist q = arccos ∘ fcos q` near such a point, using
  `Work.Diff.C.rdist_continuous` and the strict range `(0,π)`); no eikonal is needed for this step.
  The eikonal companion `⟪∇(rdist q) y, ∇(rdist q) y⟫ = 1` at every such point is
  `Work.Diff.C.rgrad_rdist_eikonal` (`Diff/C/rgrad_rdist_eikonal.lean`, proved).
* `smul_eq_smul_of_curveVelocity_eq` — two rays `GExp q (· • ξ)`, `GExp q (· • η)` (`ξ, η ≠ 0`) that
  meet at time `τ > 0` **with the same arrival velocity** must have `τ • ξ = τ • η` (geodesic
  uniqueness, `Submission.GlobalExp.eqOn_Ioo_of_isGeodesicAt_of_eq`).
* **`false_of_two_minimising`** — two *distinct minimising* rays to the same point are impossible if
  `rdist q` is `C^∞` at that point with unit gradient: the chain rule
  (`Work.Diff.C.curveVelocity_GExp_eq_smul_rgrad`) identifies both arrival velocities with
  `∇(rdist q)`, contradicting the previous lemma.  This is the "two minimising geodesics" half of
  "a cut point is not a smooth point of the distance function".

**`CutTimeGeProp` — the ODE route (this is the recommended one; it needs no cut-locus theory).**
For a unit `ξ` and the ray `γ t = GExp q (t • ξ)` (all of whose points have `rdist q (γ t) ≤ t ≤ ρ₀`,
hence are in the region where `rdist q` is `C^∞` by `RdistSmoothProp` and the *shape-operator bound*
`Work.Diff.C.rhess_rdist_bound_of_hHess` applies), set

`A t := rdist q (γ t)`,  `C t := ⟪∇(rdist q)(γ t), γ'(t)⟫`,  `Ψ t := 1 - (C t)^2 ≥ 0`.

* `A' = C` (chain rule), and `C' = Hess(rdist q)(γ t)(γ', γ') = S(t)·(1 - C²)` where
  `|S(t) - cot (A t)| ≤ ε₁ / sin (A t)`: decompose `γ' = C • ∇d + γ'⊥` (both unit vectors, so
  `‖γ'⊥‖² = 1 - C²`), use `Hess(d)(∇d, ·) = 0` (from the eikonal `|∇d| = 1`) and apply the
  shape bound to `γ'⊥ ⊥ ∇d`; the orthogonality hypothesis of `rhess_rdist_bound_of_hHess` is
  `⟪∇(fcos q), V⟫ = 0`, which is equivalent to `V ⊥ ∇(rdist q)` by `Work.Diff.C.rgrad_fcos`.
* Hence `Ψ' = -2 C (C')_err Ψ` with `|Ψ'| ≤ (2 (1+ε₁) / sin (A t)) Ψ`, and on any interval where
  `sin (A ·) ≥ m > 0` Grönwall gives `Ψ ≡ 0` from `Ψ = 0` at one point; then `C = ±1` and, by
  continuity, `C ≡ 1`, so `A = id`.
* `A = id` holds near `0` by `Work.Diff.C.ray_minimising` (short rays are minimising).  Let
  `I := {t ∈ [0, ρ₀] : C = 1 on [0,t]}`; `I` is non-empty, closed (continuity of `C` where
  `rdist q` is `C^∞`, iterated to the endpoint using that the germ hypothesis of `hsmC` gives `C²` on
  a neighbourhood), and open: at `t ∈ I` with `t < ρ₀`, `A(s) ∈ [t - δ, t + δ] ⊆ (0, ρ₀)` for small
  `δ`, so `sin (A s) ≥ m > 0` there and Grönwall forces `Ψ ≡ 0` on `[t, t+δ]`, i.e. `C ≡ 1`
  (continuity).  Hence `I = [0, ρ₀]` and `A(ρ₀) = ρ₀`, i.e. `ρ₀ ≤ cutTime q ξ`.
* `injAtLeast_of_forall_cutTime_le` then gives `InjAtLeast hmet q ρ₀`.

**`CutTimeGtProp` — why strictness.**  Only needed when `ρ = ρ₀`: there `‖ρ • (v + s • η)‖ > ρ₀`, so
one needs the ray to be minimising *strictly beyond* `ρ₀`.  With `CutTimeGeProp` at hand one may
instead use: `cutTime` is *lower semicontinuous* at every direction (`{ξ : cutTime ξ ≥ c}` is closed,
being the set where the closed condition `edist q (GExp q (c • ξ)) = ofReal c` holds; use
`Submission.CutKlingenberg`'s compactness argument with `GExp`-continuity), so it suffices that
`cutTime q v > ρ₀` for the *base* direction `v`.  That is `CutTimeGtProp` at `ξ := v`; the route is
the cut-point dichotomy as documented above.

**`HnePartProp`** is then `CutTimeGeProp` + `injAtLeast_of_forall_cutTime_le` + the witness-pair
argument (note `t < ρ ≤ ρ₀` is *strict*, so the witnesses found near `t • v` have norm `< ρ₀`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.GeoCrux

/-- **The distance function is smooth inside the ball of radius `π - arccos (1-c)`.** -/
abbrev RdistSmoothProp : Prop :=
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
    (q y : M) (hy0 : 0 < rdist (I := I) (M := M) q y)
    (hyπ : rdist (I := I) (M := M) q y < Real.pi - Real.arccos (1 - c)),
    CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) y

/-- **No cut point in the closed ball of radius `π - arccos (1-c)`.** -/
abbrev CutTimeGeProp : Prop :=
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
    (q : M) (ξ : TangentSpace I q) (hξ : Inner.inner ℝ ξ ξ = 1),
    Real.pi - Real.arccos (1 - c) ≤ Submission.CutTime.cutTime (I := I) hmet q ξ

/-- **No cut point in the closed ball, strict form.** -/
abbrev CutTimeGtProp : Prop :=
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
    (q : M) (ξ : TangentSpace I q) (hξ : Inner.inner ℝ ξ ξ = 1),
    Real.pi - Real.arccos (1 - c) < Submission.CutTime.cutTime (I := I) hmet q ξ

/-- **The second conjunct of `RadialCutProp`** (the vanishing of the radial variation field), from
the injectivity of `GExp q` on the ball of radius `π - arccos (1-c)`. -/
abbrev HnePartProp : Prop :=
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
    (q : M)
    (hinj : Submission.InjRadius.InjAtLeast (I := I) hmet q (Real.pi - Real.arccos (1 - c)))
    (v η : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (horth : Inner.inner ℝ v η = 0) (hη : η ≠ 0)
    (ρ : ℝ) (hρ : 0 < ρ) (hρle : ρ ≤ Real.pi - Real.arccos (1 - c)),
    ∀ t ∈ Set.Ioo (0 : ℝ) ρ,
      Submission.Geodesic.curveVelocity (I := I) (M := M)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + r • η))) 0
        ≠ 0

/-! ## The smoothness of the distance function (`RdistSmoothProp`) -/

/-- `cos` is `≥ -1 + c` on the region `rdist q ≤ π - arccos (1-c)`. -/
theorem neg_one_add_le_fcos_of_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) {q y : M}
    (hyπ : rdist (I := I) (M := M) q y < Real.pi - Real.arccos (1 - c)) :
    -1 + c ≤ fcos (I := I) (M := M) q y := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have harccos : Real.arccos (-1 + c) = Real.pi - Real.arccos (1 - c) := by
    have h : (-1 + c : ℝ) = -(1 - c) := by ring
    rw [h, Real.arccos_neg]
  have hle : rdist (I := I) (M := M) q y ≤ Real.arccos (-1 + c) := by
    rw [harccos]; linarith
  have hd0 : 0 ≤ rdist (I := I) (M := M) q y :=
    ENNReal.toReal_nonneg
  have harccos_le : Real.arccos (-1 + c) ≤ Real.pi := Real.arccos_le_pi _
  show -1 + c ≤ Real.cos (rdist (I := I) (M := M) q y)
  calc (-1 + c)
      = Real.cos (Real.arccos (-1 + c)) :=
        (Real.cos_arccos (by linarith) (by linarith)).symm
    _ ≤ Real.cos (rdist (I := I) (M := M) q y) :=
        Real.cos_le_cos_of_nonneg_of_le_pi hd0 harccos_le hle

/-- **The distance function is smooth inside the ball of radius `π - arccos (1-c)`)**
(the `arccos` trick: `rdist q = arccos ∘ fcos q` near such a point). -/
theorem rdist_smooth_eikonal : RdistSmoothProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hdiam q y hy0 hyπ
  have hfcos_ge : -1 + c ≤ fcos (I := I) (M := M) q y :=
    neg_one_add_le_fcos_of_le (I := I) (M := M) (c := c) hc hc1 (q := q) (y := y) hyπ
  have hsm : CMDiffAt ∞ (fcos (I := I) (M := M) q) y := hsmC q y hfcos_ge
  -- `d := rdist q y ∈ (0,π)`
  have hdpi : rdist (I := I) (M := M) q y < Real.pi := by
    have h : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
    linarith [hyπ]
  -- the composition with `arccos`
  have hfcos_ne : fcos (I := I) (M := M) q y ≠ -1 ∧ fcos (I := I) (M := M) q y ≠ 1 := by
    have hcos : fcos (I := I) (M := M) q y = Real.cos (rdist (I := I) (M := M) q y) := rfl
    constructor
    · rw [hcos]
      intro h
      have h' : Real.cos (rdist (I := I) (M := M) q y) = Real.cos Real.pi := by
        rw [h, Real.cos_pi]
      have := Real.strictAntiOn_cos.injOn ⟨hy0.le, hdpi.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ h'
      linarith
    · rw [hcos]
      intro h
      have h' : Real.cos (rdist (I := I) (M := M) q y) = Real.cos 0 := by
        rw [h, Real.cos_zero]
      have := Real.strictAntiOn_cos.injOn ⟨hy0.le, hdpi.le⟩ ⟨le_refl 0, Real.pi_pos.le⟩ h'
      linarith
  have hcos_sm : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ Real.arccos
      (fcos (I := I) (M := M) q y) :=
    (Real.contDiffAt_arccos hfcos_ne.1 hfcos_ne.2).contMDiffAt
  have harccos_sm : CMDiffAt ∞
      (fun z : M ↦ Real.arccos (fcos (I := I) (M := M) q z)) y := by
    have h := ContMDiffAt.comp (I := I) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
      (f := fcos (I := I) (M := M) q) (g := Real.arccos) y hcos_sm hsm
    exact h
  -- the two functions agree near `y`
  have hev : (fun z : M ↦ rdist (I := I) (M := M) q z) =ᶠ[𝓝 y]
      (fun z : M ↦ Real.arccos (fcos (I := I) (M := M) q z)) := by
    have hcont := rdist_continuous (I := I) (M := M) q
    have h1 : ∀ᶠ z in 𝓝 y, 0 < rdist (I := I) (M := M) q z :=
      hcont.continuousAt (isOpen_Ioi.mem_nhds hy0)
    have h2 : ∀ᶠ z in 𝓝 y, rdist (I := I) (M := M) q z < Real.pi :=
      hcont.continuousAt (isOpen_Iio.mem_nhds hdpi)
    filter_upwards [h1, h2] with z hz1 hz2
    show rdist (I := I) (M := M) q z = Real.arccos (fcos (I := I) (M := M) q z)
    rw [show fcos (I := I) (M := M) q z = Real.cos (rdist (I := I) (M := M) q z) from rfl,
      Real.arccos_cos hz1.le hz2.le]
  exact harccos_sm.congr_of_eventuallyEq hev

/-! ## Two geodesics arriving with the same velocity

This is the (easy) half of the classical "a point with two distinct minimising geodesics is not a
smooth point of the distance function": the two rays then arrive *with the same velocity*
(`= ∇(rdist q)`, by the chain rule plus Cauchy–Schwarz), and two geodesics with the same position
and velocity coincide --- so the rays are the same, contradicting the distinctness of their
directions.  The input is therefore the *arrival velocity* form, which is what the caller proves
separately.-/

/-- **Two rays with the same endpoint and the same arrival velocity coincide.**

For `ξ, η ≠ 0` and `τ > 0`, if `GExp q (τ • ξ) = GExp q (τ • η)` and the two rays arrive with the
same velocity at time `τ`, then `τ • ξ = τ • η`. -/
theorem smul_eq_smul_of_curveVelocity_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {q : M} {ξ η : TangentSpace I q} (hξ : ξ ≠ 0) (hη : η ≠ 0) {τ : ℝ} (hτ : 0 < τ)
    (hpos : Submission.GlobalExp.GExp (cov := cov) hmet q (τ • ξ)
      = Submission.GlobalExp.GExp (cov := cov) hmet q (τ • η))
    (hvel : Submission.Geodesic.curveVelocity (I := I)
        (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) τ
      = Submission.Geodesic.curveVelocity (I := I)
        (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • η)) τ) :
    τ • ξ = τ • η := by
  set γ : ℝ → M := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ) with hγ
  set σ : ℝ → M := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • η) with hσ
  have hvelγ : ∀ t : ℝ,
      Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0 := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · rw [hγ, Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet q hξ]
      exact hξ
    · rw [hγ]
      have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q hξ ht
      intro h0
      rw [h0, norm_zero] at h
      exact hξ (norm_eq_zero.mp h.symm)
  have hvelσ : ∀ t : ℝ,
      Submission.Geodesic.curveVelocity (I := I) σ t ≠ 0 := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · rw [hσ, Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet q hη]
      exact hη
    · rw [hσ]
      have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q hη ht
      intro h0
      rw [h0, norm_zero] at h
      exact hη (norm_eq_zero.mp h.symm)
  have heq : Set.EqOn γ σ (Set.Ioo (-1 : ℝ) (τ + 1)) := by
    refine Submission.GlobalExp.eqOn_Ioo_of_isGeodesicAt_of_eq (I := I) (cov := cov)
      (a := -1) (b := τ + 1) ?_ ?_ ?_ ?_ ?_ ?_ (show τ ∈ Set.Ioo (-1 : ℝ) (τ + 1) from
        ⟨by linarith, by linarith⟩) ?_ hvel
    · exact (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hξ).mono (Set.subset_univ _)
    · exact (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hη).mono (Set.subset_univ _)
    · intro t _
      exact Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet q hξ t
    · intro t _
      exact Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet q hη t
    · intro t _
      exact hvelγ t
    · intro t _
      exact hvelσ t
    · exact hpos
  have hev : γ =ᶠ[𝓝 (0 : ℝ)] σ := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < τ + 1 by linarith)] with t ht
    exact heq ht
  have hvel0 : Submission.Geodesic.curveVelocity (I := I) γ 0
      = Submission.Geodesic.curveVelocity (I := I) σ 0 :=
    Submission.RayJacobi.curveVelocity_congr (I := I) hev
  rw [hγ, Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet q hξ] at hvel0
  rw [hσ, Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet q hη] at hvel0
  rw [hvel0]

/-- **Two distinct minimising rays to the same point are impossible when `rdist q` is `C^∞` and
eikonal there.**

If `u ≠ v` with `GExp q u = GExp q v` and both rays minimising (`edist = ofReal ‖·‖`), and `rdist q`
is `C^∞` at the common endpoint with unit gradient, we reach a contradiction: the chain rule
identifies the arrival velocity of each ray with `∇(rdist q)` — via
`Work.Diff.C.curveVelocity_GExp_eq_smul_rgrad` — and `smul_eq_smul_of_curveVelocity_eq` then forces
`u = v`. -/
theorem false_of_two_minimising
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {u v : TangentSpace I q} (huv : u ≠ v)
    (hGu : Submission.GlobalExp.GExp (cov := cov) hmet q u
      = Submission.GlobalExp.GExp (cov := cov) hmet q v)
    (hminu : Manifold.riemannianEDist I q (Submission.GlobalExp.GExp (cov := cov) hmet q u)
      = ENNReal.ofReal ‖u‖)
    (hminv : Manifold.riemannianEDist I q (Submission.GlobalExp.GExp (cov := cov) hmet q v)
      = ENNReal.ofReal ‖v‖)
    (hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z)
      (Submission.GlobalExp.GExp (cov := cov) hmet q u))
    (heik : Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q u))
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q u)) = 1) :
    False := by
  -- the equal norms
  have hnorm : ‖u‖ = ‖v‖ := by
    have h1 : ENNReal.ofReal ‖u‖ = ENNReal.ofReal ‖v‖ := by
      rw [← hminu, ← hminv, hGu]
    have h2 : ‖u‖ ≤ ‖v‖ := (ENNReal.ofReal_le_ofReal_iff (norm_nonneg v)).mp h1.le
    have h3 : ‖v‖ ≤ ‖u‖ := (ENNReal.ofReal_le_ofReal_iff (norm_nonneg u)).mp h1.ge
    exact le_antisymm h2 h3
  -- non-zero directions
  have hu0 : u ≠ 0 := by
    intro h0
    have hzv : Submission.GlobalExp.GExp (cov := cov) hmet q v = q := by
      rw [← hGu, h0, Submission.GlobalExp.GExp_zero]
    have h2 : ENNReal.ofReal ‖v‖ = 0 := by
      rw [← hminv, hzv, Manifold.riemannianEDist_self]
    have h3 : ‖v‖ = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp h2) (norm_nonneg v)
    exact huv (by rw [h0, norm_eq_zero.mp h3])
  have hv0 : v ≠ 0 := by
    intro h0
    have : ‖u‖ = 0 := by rw [hnorm, h0, norm_zero]
    exact hu0 (norm_eq_zero.mp this)
  -- the arrival velocities
  have hvelu := Work.Diff.C.curveVelocity_GExp_eq_smul_rgrad (I := I) (M := M) (cov := cov) hmet
    hu0 hminu (by rw [one_smul]; exact hsm) (by rw [one_smul]; exact heik)
  have hsmv : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z)
      (Submission.GlobalExp.GExp (cov := cov) hmet q ((1 : ℝ) • v)) := by
    rw [one_smul, ← hGu]
    exact hsm
  have hvelv := Work.Diff.C.curveVelocity_GExp_eq_smul_rgrad (I := I) (M := M) (cov := cov) hmet
    hv0 hminv hsmv (by rw [one_smul, ← hGu]; exact heik)
  have hvel_eq : Submission.Geodesic.curveVelocity (I := I)
        (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) 1
      = Submission.Geodesic.curveVelocity (I := I)
        (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) 1 := by
    rw [hvelu, hvelv, hnorm, one_smul, one_smul, hGu]
  have hpos : Submission.GlobalExp.GExp (cov := cov) hmet q ((1 : ℝ) • u)
      = Submission.GlobalExp.GExp (cov := cov) hmet q ((1 : ℝ) • v) := by
    rw [one_smul, one_smul]; exact hGu
  have hfinal := smul_eq_smul_of_curveVelocity_eq (I := I) (M := M) (cov := cov) hmet hu0 hv0
    (show (0 : ℝ) < 1 by norm_num) hpos hvel_eq
  rw [one_smul, one_smul] at hfinal
  exact huv hfinal

/-! ## The Hessian of a function is blind in the direction of its own gradient -/

/-- **`Hess F (∇F, X) = 0` where `|∇F|` is constant.**

If `F` is `C^∞` at `x` and `⟪∇F, ∇F⟫ ≡ 1` near `x`, then the Hessian of `F` vanishes on the first
pair `(∇F, X)`, for every `X`.  Proof: `Hess F (∇F, X) = Hess F (X, ∇F)` (symmetry of the Hessian,
`Work.Diff.C.rhess_symm`) `= ⟪∇_X∇F, ∇F⟫ = ½ X(⟪∇F,∇F⟫) = 0`, using the pointwise metric
compatibility `Work.Diff.C.mvfderiv_inner_eq_of_isMetricCompatible` and the fact that
`⟪∇F, ∇F⟫ ≡ 1` on a neighbourhood (so its derivative vanishes). -/
theorem rhess_rgrad_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {F : M → ℝ} {x : M} (hF : CMDiffAt ∞ F x)
    (heik : ∀ᶠ y in 𝓝 x, Inner.inner ℝ (rgrad (I := I) F y) (rgrad (I := I) F y) = 1)
    (X : TangentSpace I x) :
    Work.Diff.C.rhess cov F x (rgrad (I := I) F x) X = 0 := by
  rw [Work.Diff.C.rhess_symm (I := I) (cov := cov) hmet htor hF (rgrad (I := I) F x) X]
  show Inner.inner ℝ (cov (fun y : M ↦ rgrad (I := I) F y) x X) (rgrad (I := I) F x) = 0
  have hσmd : MDiffAt (T% (fun y : M ↦ rgrad (I := I) F y)) x :=
    (Work.Diff.C.grad_smoothAt (I := I) (F := F) (x := x) hF).mdifferentiableAt (by simp)
  have hkey := Work.Diff.C.mvfderiv_inner_eq_of_isMetricCompatible (I := I) (cov := cov)
    hmet hσmd hσmd X
  have hzero : mvfderiv I
      (fun y : M ↦ Inner.inner ℝ (rgrad (I := I) F y) (rgrad (I := I) F y)) x X = 0 := by
    rw [Work.Diff.GE.mvfderiv_congr_of_eventuallyEq_real (I := I) (x := x)
      (f := fun y : M ↦ Inner.inner ℝ (rgrad (I := I) F y) (rgrad (I := I) F y))
      (g := fun _ : M => (1 : ℝ)) heik]
    simp [mvfderiv_const]
  rw [hkey] at hzero
  have h2 : Inner.inner ℝ (cov (fun y : M ↦ rgrad (I := I) F y) x X) (rgrad (I := I) F x)
      + Inner.inner ℝ (rgrad (I := I) F x) (cov (fun y : M ↦ rgrad (I := I) F y) x X) = 0 :=
    hzero
  rw [real_inner_comm (x := rgrad (I := I) F x)
    (y := cov (fun y : M ↦ rgrad (I := I) F y) x X)] at h2
  linarith

/-- `rhess` is additive in its first slot (definitional: it is an inner product). -/
theorem rhess_add_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} {F : M → ℝ}
    {x : M} (V₁ V₂ W : TangentSpace I x) :
    Work.Diff.C.rhess cov F x (V₁ + V₂) W
      = Work.Diff.C.rhess cov F x V₁ W + Work.Diff.C.rhess cov F x V₂ W := by
  simp only [Work.Diff.C.rhess, map_add, inner_add_left]

/-- `rhess` is additive in its second slot. -/
theorem rhess_add_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} {F : M → ℝ}
    {x : M} (V W₁ W₂ : TangentSpace I x) :
    Work.Diff.C.rhess cov F x V (W₁ + W₂)
      = Work.Diff.C.rhess cov F x V W₁ + Work.Diff.C.rhess cov F x V W₂ := by
  simp only [Work.Diff.C.rhess, inner_add_right]

/-- `rhess` is homogeneous in its first slot. -/
theorem rhess_smul_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} {F : M → ℝ}
    {x : M} (a : ℝ) (V W : TangentSpace I x) :
    Work.Diff.C.rhess cov F x (a • V) W = a * Work.Diff.C.rhess cov F x V W := by
  simp only [Work.Diff.C.rhess, map_smul, real_inner_smul_left]

/-- `rhess` is homogeneous in its second slot. -/
theorem rhess_smul_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} {F : M → ℝ}
    {x : M} (a : ℝ) (V W : TangentSpace I x) :
    Work.Diff.C.rhess cov F x V (a • W) = a * Work.Diff.C.rhess cov F x V W := by
  simp only [Work.Diff.C.rhess, inner_smul_right]

/-- **The Hessian of `F` sees only the component of `W` orthogonal to `∇F`.**

If `F` is `C^∞` at `x` with `⟪∇F, ∇F⟫ ≡ 1` near `x`, then
`Hess F x (W, W) = Hess F x (W - ⟪∇F, W⟫ • ∇F, W - ⟪∇F, W⟫ • ∇F)`. -/
theorem rhess_eq_rhess_sub_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {F : M → ℝ} {x : M} (hF : CMDiffAt ∞ F x)
    (heik : ∀ᶠ y in 𝓝 x, Inner.inner ℝ (rgrad (I := I) F y) (rgrad (I := I) F y) = 1)
    (W : TangentSpace I x) :
    Work.Diff.C.rhess cov F x W W
      = Work.Diff.C.rhess cov F x (W - (Inner.inner ℝ (rgrad (I := I) F x) W) • rgrad (I := I) F x)
          (W - (Inner.inner ℝ (rgrad (I := I) F x) W) • rgrad (I := I) F x) := by
  set g : TangentSpace I x := rgrad (I := I) F x with hg
  set C : ℝ := Inner.inner ℝ g W with hC
  have hgg : Inner.inner ℝ g g = 1 := heik.self_of_nhds
  have hzerog : ∀ X : TangentSpace I x, Work.Diff.C.rhess cov F x g X = 0 :=
    fun X => rhess_rgrad_eq_zero (I := I) (cov := cov) hmet htor hF heik X
  have hzerog' : ∀ X : TangentSpace I x, Work.Diff.C.rhess cov F x X g = 0 := fun X =>
    (Work.Diff.C.rhess_symm (I := I) (cov := cov) hmet htor hF X g).trans (hzerog X)
  have hsub : W = (W - C • g) + C • g := by rw [sub_add_cancel]
  have hstep : Work.Diff.C.rhess cov F x W W
      = Work.Diff.C.rhess cov F x ((W - C • g) + C • g) ((W - C • g) + C • g) :=
    congrArg₂ (fun a b => Work.Diff.C.rhess cov F x a b) hsub hsub
  rw [hstep, rhess_add_left, rhess_add_right, rhess_add_right]
  have h1 : Work.Diff.C.rhess cov F x (W - C • g) (C • g) = 0 := by
    rw [rhess_smul_right, hzerog', mul_zero]
  have h2 : Work.Diff.C.rhess cov F x (C • g) (W - C • g) = 0 := by
    rw [rhess_smul_left, hzerog, mul_zero]
  have h3 : Work.Diff.C.rhess cov F x (C • g) (C • g) = 0 := by
    rw [rhess_smul_left, rhess_smul_right, hzerog, mul_zero, mul_zero]
  rw [h1, h2, h3, add_zero, add_zero, add_zero]

end Work.Diff.C.GeoCrux
