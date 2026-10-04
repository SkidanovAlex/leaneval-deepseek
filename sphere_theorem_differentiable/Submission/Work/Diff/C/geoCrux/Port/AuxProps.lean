import Mathlib
import Submission.Work.Diff.C.geoCrux.Port.Core

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Closed `Prop` statements of the auxiliary shape/surjectivity facts for the two-centre core

This module collects, as closed `abbrev`s, the three auxiliary geometric facts that the proof of
`Work.Diff.C.geoCrux.Port.TwoCentreCoreProp` (`Submission/Work/Diff/C/geoCrux/twoCentreCore.lean`) uses,
so that they can be delegated (the delegation harness elaborates a submitted statement in a file
that contains only the `depends_on` imports and **no** `open` commands, and in that bare context the
notation `∞` and the Riemannian-bundle binders do not elaborate).

Throughout, `q : M`, `v ∈ T_qM` is a *unit* vector (`hv0 : v ≠ 0` is a consequence),
`gam s = tcGam hmet q v s = GExp q (s • v)` is the unit-speed geodesic ray out of `q`,
`p_t := tcGam hmet q v t = GExp q (t • v)`, and `tcPrayFld hmet q v t η` is the *forward* variation
field of the family of rays out of `p_t` in the reversed direction `-γ'(t)` (so its value at
`u = 0` is `0` and its covariant derivative there is `η`); see the docstring of
`Submission/Work/Diff/C/geoCrux/TwoCentre/Setup.lean`.

* `tcPrayFldSurjBaseProp` — surjectivity of `η ↦ tcPrayFld hmet q v t η t`, i.e. every
  `W ⊥ v` is the value at `q` of the backward field from `p_t` with a suitable (tangential)
  initial derivative `η ⊥ γ'(t)`.  It is the `u = t` case of `Work.Diff.C.geoCrux.tcPrayFld_surj`
  (`tc_exists_equiv` at `u = t`, where `‖t • (-γ'(t))‖ = t < rho0 c`).

* `tcBaseShapeProp` — the **shape relation at the base point**: the `σ → 0` case of
  `Work.Diff.C.geoCrux.tcBwd_shape_gam`, i.e. the covariant derivative at `q` of the backward field
  from `p_t` equals `- Hess (rdist p_t)(q)` applied to its value at `q`.
  Equivalently (this is the form used) `∇_s (s ↦ tcPrayFld hmet q v t η (t - s))` at `s = 0`
  is `- Hess (rdist p_t)(q) (tcPrayFld hmet q v t η t)`.

* `tcFwdShapeProp` — the shape identity for the *forward* family with an arbitrary second argument:
  for `ξ ⊥ v` and `X ⊥ γ'(σ)`,
  `⟪∇_s (tcFwd hmet q v ξ)(σ), X⟫ = Hess (rdist q)(p_σ)(tcFwd hmet q v ξ σ, X)`.
  It is `Work.Diff.C.geoCrux.tcFwd_bridge_bilin` (the polarised form of the `dmRadialBridge`
  identity) combined with the surjectivity of the forward family
  (`Work.Diff.C.geoCrux.tc_exists_equiv` at the ray direction `σ • v`, `σ < rho0 c`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.geoCrux.Port

/-- **Surjectivity of the backward family at the base point.**  For every `W ⊥ v` there is a
tangential initial derivative `η ⊥ γ'(t)` whose backward field from `p_t = γ(t)` takes the value `W`
at `q = γ(0)`.

This is the `u = t` case of `Work.Diff.C.geoCrux.tcPrayFld_surj`; the proof is the same
(`tcPrayFld hmet q v t η u = d(GExp p_t)(u • (-γ'(t)))(u • η)`, `mfderiv` invertible at
`t • (-γ'(t))` since `‖t • (-γ'(t))‖ = t < rho0 c`, and `tcPrayFld_gauss` at `u = t` identifies the
orthogonality condition). -/
abbrev tcPrayFldSurjBaseProp : Prop :=
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
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht : t < rho0 c)
    (W : TangentSpace I q) (hW : tcIn (M := M) (I := I) q v W = 0),
    ∃ η : TangentSpace I (tcGam (cov := cov) hmet q v t),
      tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v t) η
          (-(tcVel (cov := cov) hmet q v t)) = 0 ∧
      tcPrayFld (cov := cov) hmet q v t η t = W

/-- **The shape relation at the base point.**  The covariant derivative at `q = γ(0)` of the
backward field `s ↦ tcPrayFld hmet q v t η (t - s)` (a Jacobi field along `γ`, vanishing at
`p_t = γ(t)`) satisfies, for every `X ⊥ v`,

`⟪∇_s (s ↦ tcPrayFld hmet q v t η (t - s)) (0), X⟫ = - Hess (rdist p_t)(q) (J η t, X)`.

This is `Work.Diff.C.geoCrux.tcBwd_shape_gam` with `σ := 0`; the proof is the `u = t` case of the
chain `tcPrayFld_bridge` (`dmRadialBridge` with `d := t > 0`, `tc_minW_bwd` for the minimisation,
`rgrad_rdist_back` for the gradient) ⟶ `tcPrayFld_bridge_bilin` (polarisation + the Wronskian
antisymmetry `tc_wronskian_const`) ⟶ `tcPrayFld_shape_all` (surjectivity of the second argument at
`u = t`, i.e. `tcPrayFldSurjBaseProp`) ⟶ `covAlong_comp_sub` to return to the `s`-parametrisation. -/
abbrev tcBaseShapeProp : Prop :=
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
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht : t < rho0 c)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v t))
    (hη : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v t) η
      (-(tcVel (cov := cov) hmet q v t)) = 0)
    (X : TangentSpace I q) (hX : tcIn (M := M) (I := I) q v X = 0),
    tcIn (M := M) (I := I) q
        (Submission.JacobiGlobal.covAlong cov
          (γ := tcGam (cov := cov) hmet q v)
          (fun s : ℝ => tcPrayFld (cov := cov) hmet q v t η (t - s)) 0) X
      = - rhess cov (fun z : M ↦ rdist (I := I) (M := M)
            (tcGam (cov := cov) hmet q v t) z)
          q (tcPrayFld (cov := cov) hmet q v t η t) X

/-- **The shape identity for the forward family, arbitrary second argument.**  For `ξ ⊥ v` and
`X ⊥ γ'(σ)` (with `0 < σ < rho0 c`),

`⟪∇_s (tcFwd hmet q v ξ)(σ), X⟫ = Hess (rdist q)(γ(σ))(tcFwd hmet q v ξ σ, X)`.

The proof is `Work.Diff.C.geoCrux.tcFwd_bridge_bilin` (the polarised `dmRadialBridge` identity for
two forward fields), together with the surjectivity of the forward family at `σ`: for
`X ⊥ γ'(σ)` the `u = σ` case of `Work.Diff.C.geoCrux.tc_exists_equiv` (the `mfderiv` of `GExp q` at
`σ • v` is invertible since `‖σ • v‖ = σ < rho0 c`) and `tcFwd_gauss` produce `ξ' ⊥ v` with
`tcFwd hmet q v ξ' σ = X`. -/
abbrev tcFwdShapeProp : Prop :=
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
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ < rho0 c)
    (ξ : TangentSpace I q) (hξ : tcIn (M := M) (I := I) q v ξ = 0)
    (X : TangentSpace I (tcGam (cov := cov) hmet q v σ))
    (hX : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) X
      (tcVel (cov := cov) hmet q v σ) = 0),
    tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (Submission.JacobiGlobal.covAlong cov
          (γ := tcGam (cov := cov) hmet q v) (tcFwd (cov := cov) hmet q v ξ) σ) X
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v ξ σ) X

end Work.Diff.C.geoCrux.Port

namespace Work.Diff.C.geoCrux.Port

/-- **`IsJacobiAt` is invariant under reversing the parametrisation of the curve and the field.**
If `J` is a Jacobi field along `γ` near every time, then `s ↦ J (T - s)` is a Jacobi field along
`s ↦ γ (T - s)`.

This is a chart-level statement: given the chart data `(x₀,u,w,y)` of `(γ,J)` at `T - t`, the data
`(x₀, u ∘ (T - ·), -(w ∘ (T - ·)), y ∘ (T - ·))` realises `(t ↦ γ (T - t), t ↦ J (T - t))` at `t`.
The two sign flips in `chartCovDeriv` (one from `deriv y` and one from the Christoffel pairing) cancel,
and `chartCurv` is quadratic in the velocity, so the chart Jacobi equation is preserved. -/
abbrev IsJacobiAtRevProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    (hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ J t) (T t : ℝ),
    Submission.RauchGlobal.IsJacobiAt cov (fun s : ℝ => γ (T - s))
      (fun s : ℝ => J (T - s)) t

end Work.Diff.C.geoCrux.Port
