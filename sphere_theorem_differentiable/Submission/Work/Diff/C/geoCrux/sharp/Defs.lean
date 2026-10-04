import Mathlib
import Submission.Work.Diff.C.geoCrux.CoreStmts
import Submission.Work.Diff.C.geoCrux.SharpCore

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Statements of the pieces of the sharp radial modulus bound

This module collects, as closed `abbrev`s, the two geometric inputs of the sharp radial modulus
bound (`Work.Diff.C.geoCrux.radial_modulus_sharp`) that are obtained from the two-centre core
(`Work.Diff.C.geoCrux.TwoCentreCoreProp`) and from the injectivity radius.  They are stated in the
"closed `Prop`" style so that they can be delegated (the delegation harness elaborates a submitted
statement in a file that imports only the `depends_on` modules and has no `open` commands).

* `SharpAnchorProp` — **the anchor**: for `2σ ≤ ρ₀ = π - arccos (1-c)` and `cos σ ≥ 1/2` (so
  `σ ≤ π/3`), the radial variation field satisfies
  `‖Z_ξ(σ)‖ ≤ sin σ (1 + 7ε₁) ‖ξ‖` for every `ξ ⊥ v`.  It is `Work.Diff.C.geoCrux.modulus_of_twoCentre`
  fed with the two-centre inequalities of `TwoCentreCoreProp` at the pair `(σ, 2σ)` (where
  `κλ = 1/sin²σ`, `η ≤ 3ε₁λ`, `δ ≤ 3ε₁κ`, all proved in `geoCrux/radial_modulus.lean`).

* `SharpNeZeroProp` — **non-vanishing of the radial variation field**: `Z_ξ(t) ≠ 0` for
  `0 < t ≤ ρ₀` and `0 ≠ ξ ⊥ v`.  For `t < ρ₀` this is the injectivity of `d (GExp q)` at `t • v`
  (from `hcut`); the endpoint `t = ρ₀` follows from
  `Work.Diff.C.no_conjTime_le_arccos` together with the shape-operator bound
  (`Work.Diff.C.rhess_rdist_bound_of_hHess`) and the bridge `Work.Diff.C.dmRadialBridge` (the ray is
  minimising up to `ρ₀` by `Work.Diff.C.geoCrux.InjCore.ray_minimising_upto'`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.geoCrux

/-- **The anchor of the sharp modulus bound.**  For `0 < σ` with `2σ ≤ ρ₀ = π - arccos (1-c)` and
`cos σ ≥ 1/2`, and every `ξ ⊥ v` (where `v ∈ T_qM` is a unit vector),

`‖Z_ξ(σ)‖ ≤ sin σ (1 + 7ε₁) ‖ξ‖`,  `Z_ξ(s) = ∂_r|₀ GExp q (s • (v + r • ξ))`.

These `σ` are exactly those `≤ π/3` (since `ρ₀ > 2π/3` for `c ≤ 1/4`), and the bound is the output
of the two-centre argument at the pair `(σ, 2σ)`. -/
abbrev SharpAnchorProp : Prop :=
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
    (σ : ℝ) (hσ0 : 0 < σ) (h2σ : 2 * σ ≤ Real.pi - Real.arccos (1 - c))
    (hcos : 1 / 2 ≤ Real.cos σ)
    (ξ : TangentSpace I q) (hξ : Inner.inner ℝ v ξ = 0),
    ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
        (σ • (v + r • ξ))) 0‖
      ≤ Real.sin σ * (1 + 7 * ε₁) * ‖ξ‖

/-- **Non-vanishing of the radial variation field below `ρ₀`.**  For a unit `v ∈ T_qM`, `ξ ⊥ v` with
`ξ ≠ 0`, and `0 < t ≤ ρ₀ = π - arccos (1-c)`:

`∂_r|₀ GExp q (t • (v + r • ξ)) ≠ 0`.

For `t < ρ₀` this says that `d (GExp q)` is invertible at `t • v` (injectivity radius), for
`t = ρ₀` that there is no conjugate point at distance `ρ₀ < π`. -/
abbrev SharpNeZeroProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
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
    (ξ : TangentSpace I q) (hξ : Inner.inner ℝ v ξ = 0) (hξ0 : ξ ≠ 0)
    (t : ℝ) (ht0 : 0 < t) (htρ : t ≤ Real.pi - Real.arccos (1 - c)),
    Submission.Geodesic.curveVelocity (I := I) (M := M)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
        (t • (v + r • ξ))) 0 ≠ 0

/-- **The ray package.**  Along the unit ray `γ t = GExp q (t • v)`, at every time
`t ∈ (0, ρ₀)` (`ρ₀ = π - arccos (1-c)`), from the C-area hypotheses alone:

* `rdist q` is `C^∞` at `γ t`;
* the ray is minimising: `rdist q (γ t) = t`;
* the gradient of the distance is the velocity of the ray: `∇(rdist q)(γ t) = γ'(t)`;
* orthogonality transfers from `∇(rdist q)` to `∇(fcos q) = ∇(cos ∘ rdist q)`;
* **the bridge**: the covariant derivative of the radial variation field
  `Z_ξ(s) = ∂_r|₀ GExp q (s • (v + r • ξ))` (`ξ ⊥ v`) is the shape operator,
  `⟪∇Z_ξ(t), Z_ξ(t)⟫ = rhess (rdist q)(γ t)(Z_ξ(t), Z_ξ(t))`.

The first four are `Work.Diff.C.geoCrux.InjCore.rdist_smooth_ball`,
`Work.Diff.C.geoCrux.InjCore.ray_minimising_upto'`, the Cauchy–Schwarz equality of `rayC = 1`
(from `Work.Diff.C.geoCrux.InjCore.ray_pointwise'` and the eikonal) with
`Work.Diff.C.rgrad_fcos`; the bridge is `Work.Diff.C.dmRadialBridge` (its `hminW` input is again
`ray_minimising_upto'` applied to the normalised perturbed direction). -/
abbrev SharpRayProp : Prop :=
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
    (q : M) (v : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (t : ℝ) (ht0 : 0 < t) (htρ : t < Real.pi - Real.arccos (1 - c)),
    CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) ∧
    rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) = t ∧
    rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
      = Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t ∧
    (∀ V : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)),
      Inner.inner ℝ (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))) V = 0 →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))) V = 0) ∧
    (∀ ξ : TangentSpace I q, Inner.inner ℝ v ξ = 0 →
      Inner.inner ℝ
        (Submission.JacobiGlobal.covAlong cov
          (γ := fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (s • v))
          (fun s : ℝ ↦ (show TangentSpace I
            (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) from
              fv (cov := cov) hmet q v ξ s)) t)
        ((show TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) from
          fv (cov := cov) hmet q v ξ t))
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
          ((show TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) from
            fv (cov := cov) hmet q v ξ t))
          ((show TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) from
            fv (cov := cov) hmet q v ξ t)))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **The radial variation field** of the family of rays out of `q`, as a field along the ray
`t ↦ GExp q (t • v)`: `Zf t = ∂_r|₀ GExp q (t • (v + r • ξ))`.  (Same body as
`Work.Diff.C.geoCrux.fv`.) -/
noncomputable def Zf (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) :
    (t : ℝ) → TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) :=
  fun t => Submission.Geodesic.curveVelocity (I := I)
    (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + r • ξ))) 0

/-- **The log-derivative of the radial variation field is bounded by the shape operator.**  For a
unit `v`, `ξ ⊥ v` and `t ∈ (0, ρ₀)` (`ρ₀ = π - arccos (1-c)`) the function
`t ↦ log ‖Zf t‖` has derivative `⟪∇Z_ξ(t), Z_ξ(t)⟫ / ⟪Z_ξ(t), Z_ξ(t)⟫` at `t`, and that quotient is
at most `cot t + ε₁/sin t`.

The first half is `Work.Diff.C.jld_log_deriv_of_jacobi` (with `log (‖Z‖²)/2 = log ‖Z‖`); the second
is the `SharpRayProp` bridge combined with the shape-operator bound
`Work.Diff.C.rhess_rdist_bound_of_hHess` (which needs the orthogonality
`⟪∇(fcos q)(γ t), Z_ξ(t)⟫ = 0`, supplied by the Gauss pairing
`Work.OddBound.longHomotopy.gauss_pairing_fibre` and the orthogonality transfer of
`SharpRayProp`). -/
abbrev SharpLogDerivProp : Prop :=
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
    (ξ : TangentSpace I q) (hξ : Inner.inner ℝ v ξ = 0) (hξ0 : ξ ≠ 0)
    (t : ℝ) (ht0 : 0 < t) (htρ : t < Real.pi - Real.arccos (1 - c)),
    HasDerivAt (fun s : ℝ => Real.log ‖Zf (cov := cov) hmet q v ξ s‖)
      (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov (Zf (cov := cov) hmet q v ξ) t)
          (Zf (cov := cov) hmet q v ξ t)
        / Inner.inner ℝ (Zf (cov := cov) hmet q v ξ t) (Zf (cov := cov) hmet q v ξ t)) t ∧
    Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov (Zf (cov := cov) hmet q v ξ) t)
        (Zf (cov := cov) hmet q v ξ t)
      / Inner.inner ℝ (Zf (cov := cov) hmet q v ξ t) (Zf (cov := cov) hmet q v ξ t)
      ≤ Real.cot t + ε₁ / Real.sin t

/-- The two points of the ray are equal (the raw variation field lives at the second one). -/
lemma ray_pt (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) (t : ℝ) :
    Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)
      = Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + (0 : ℝ) • ξ)) := by
  rw [zero_smul, add_zero]

/-- The norm of `Zf` is the norm of the raw velocity field. -/
lemma Zf_norm_eq (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) (t : ℝ) :
    ‖Zf (cov := cov) hmet q v ξ t‖
      = ‖Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
            (t • (v + r • ξ))) 0‖ := by
  rw [ray_pt hmet q v ξ t]
  rfl

/-- The non-vanishing of `Zf` is that of the raw velocity field. -/
lemma Zf_ne_zero_iff (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) (t : ℝ) :
    Zf (cov := cov) hmet q v ξ t = 0 ↔
      Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
          (t • (v + r • ξ))) 0 = 0 := by
  rw [ray_pt hmet q v ξ t]
  rfl

/-- **The two-centre inequalities at the pair `(σ, 2σ)`.**

For a unit `v ∈ T_qM`, `0 < σ` with `2σ ≤ ρ₀ = π - arccos (1-c)` and `cos σ ≥ 1/2`, writing
`Z_ξ(s) = ∂_r|₀ GExp q (s • (v + r • ξ))` for `ξ ⊥ v` there is `N ≥ 0` with

* `‖Z_ξ(σ)‖ ≤ N ‖ξ‖` for all `ξ ⊥ v`;
* `0 < twoK σ (2σ)`, `0 < twoL σ (2σ)`;
* `(twoK σ (2σ) - twoD ε₁ σ (2σ)) * (twoL σ (2σ) - twoE ε₁ σ (2σ)) * N ^ 2 ≤ 1`;
* for every unit `w ⊥ v`:
  `1 ≤ (twoK + twoD)(twoL ‖Z_w(σ)‖² + twoE N ‖Z_w(σ)‖)` and
  `1 ≥ (twoK - twoD)(twoL ‖Z_w(σ)‖² - twoE N ‖Z_w(σ)‖)`.

This is the body of `Work.Diff.C.geoCrux.TwoCentreCoreProp` at the pair `(σ, 2σ)` (the case
`τ = 2σ` used by the anchor of the sharp radial modulus bound), with the fields `Z_ξ` written
through the (ascribed) definition `Zf`.  It is the conclusion of the two-centre Wronskian argument:
the forward variation field `Z_ξ` out of `q` and the backward field `J_w` from the second centre
`γ(2σ)` (vanishing at `γ(2σ)`, with value `w` at `q`) have constant Wronskian `⟪ξ, w⟫`, and the two
shape identities make `⟪(S_q(σ) + S_{γ(2σ)}(σ)) Z_w(σ), J_w(σ)⟫ = ‖w‖²`, while the fundamental-solution
algebra gives `J_w(σ) = λ Z_w(σ) + Z_{Δ w}(σ)`. -/
abbrev TwoCentreSharpProp : Prop :=
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
    (σ : ℝ) (hσ0 : 0 < σ) (h2σ : 2 * σ ≤ Real.pi - Real.arccos (1 - c))
    (hcos : 1 / 2 ≤ Real.cos σ),
    ∃ N : ℝ, 0 ≤ N ∧
      (∀ ξ : TangentSpace I q, Inner.inner ℝ v ξ = 0 →
        ‖Zf (cov := cov) hmet q v ξ σ‖ ≤ N * ‖ξ‖) ∧
      0 < twoK σ (2 * σ) ∧ 0 < twoL σ (2 * σ) ∧
      (twoK σ (2 * σ) - twoD ε₁ σ (2 * σ)) *
        (twoL σ (2 * σ) - twoE ε₁ σ (2 * σ)) * N ^ 2 ≤ 1 ∧
      (∀ w : TangentSpace I q, Inner.inner ℝ v w = 0 → Inner.inner ℝ w w = 1 →
        1 ≤ (twoK σ (2 * σ) + twoD ε₁ σ (2 * σ)) *
              (twoL σ (2 * σ) * ‖Zf (cov := cov) hmet q v w σ‖ ^ 2
                + twoE ε₁ σ (2 * σ) * N * ‖Zf (cov := cov) hmet q v w σ‖) ∧
        1 ≥ (twoK σ (2 * σ) - twoD ε₁ σ (2 * σ)) *
              (twoL σ (2 * σ) * ‖Zf (cov := cov) hmet q v w σ‖ ^ 2
                - twoE ε₁ σ (2 * σ) * N * ‖Zf (cov := cov) hmet q v w σ‖))

end Work.Diff.C.geoCrux
