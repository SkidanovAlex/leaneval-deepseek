import Mathlib
import Submission.Work.Diff.C.RadialBound.FarParam

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.C.RadialBound

open Bundle
open scoped Manifold

/-! ## Transport lemmas for the tangent-space type synonym

`TangentSpace I x` is a non-reducible type synonym for the model space `E`, so the fibre metric and
the fibre norm at `x` and at `y` are *propositionally* equal when `x = y`, but not definitionally.
The three lemmas below are the transports used by the main proof: they move a norm, an inner
product, and the covariant derivative `covAlong` across a propositional equality of base points. -/

/-- The norm of a tangent vector is insensitive to a propositional equality of base points. -/
private theorem norm_congr_point'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {X Y : M} (h : X = Y) (a : E) :
    ‖(show TangentSpace I X from a)‖ = ‖(show TangentSpace I Y from a)‖ := by
  subst h; rfl

/-- The inner product of two tangent vectors at a point is insensitive to a propositional equality
of base points. -/
private theorem inner_congr_point'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {X Y : M} (h : X = Y) (a b : E) :
    Inner.inner ℝ (show TangentSpace I X from a) (show TangentSpace I X from b)
      = Inner.inner ℝ (show TangentSpace I Y from a) (show TangentSpace I Y from b) := by
  subst h; rfl

/-- **`covAlong` is invariant under rewriting the base curve and the field.**  A `covAlong` depends
on its curve and on the values of the field only, so two curves equal as functions with the same
field values give the same covariant derivative. -/
private theorem covAlong_congr_curve'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {γ₁ γ₂ : ℝ → M} (h : γ₁ = γ₂)
    {V₁ : (t : ℝ) → TangentSpace I (γ₁ t)} {V₂ : (t : ℝ) → TangentSpace I (γ₂ t)}
    (hV : ∀ t : ℝ, (show E from V₁ t) = (show E from V₂ t)) (d : ℝ) :
    Submission.JacobiGlobal.covAlong cov V₁ d
      = Submission.JacobiGlobal.covAlong cov V₂ d := by
  subst h
  rw [show V₁ = V₂ from funext hV]

open Bundle in
/-- **The differential of the radius-`ρ` exponential map at `q`.**

Let `u : T_qM` be a unit vector, `w ⊥ u`, and suppose (as a hypothesis `hmod`, supplied in the
application by `Work.Diff.C.radial_modulus_bound`) that along the ray
`γ_v (t) = GExp q (t • v)` every Jacobi field `Z` with `Z 0 = 0` and `∇_{γ'}Z(0) ⊥ v` satisfies
`‖Z ρ‖ ≤ (sin ρ + 25 ε₁)‖∇_{γ'}Z(0)‖`.  Then

`‖ ⅆ (u ↦ GExp q (ρ • u)) (u) (w) ‖ ≤ (sin ρ + 25 ε₁) ‖w‖`.

This is the reduction of the differential of the "far sphere parametrisation" `Φ u = GExp q (ρ • u)`
to the radial Jacobi field: with `w' := ρ w`, the variation field of `r ↦ GExp q (t • (u + r η))`,
`η := w` (i.e. `Z(t) = ⅆ(GExp q)(t • u)[t • η]`, `Z 0 = 0`, `∇Z(0) = w`) has
`Z ρ = ⅆ(GExp q)(ρ • u)[ρ w] = ⅆΦ(u)[w]`, so `hmod` applied to it gives the claim directly (the two
factors of `ρ` from `ⅆΦ = ⅆGExp ∘ (ρ • ·)` and from `Z'(0) = w = w'/ρ` cancel).  The construction of
`Z` is `Submission.Work.Diff.C.hess_dist_jacobi_shapeOp_mfderiv` (which does *not* record its initial
derivative and must be re-derived from the definition, or the field be rebuilt from
`Commons.Analysis.ODE.exists_linearODE_solution_Icc`); the chain rule
`ⅆΦ(u)[w] = ⅆ(GExp q)(ρ • u)[ρ • w]` is `mfderiv_comp` with the linear map `x ↦ ρ • x`. -/
theorem GExp_radius_mfderiv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ Work.Diff.C.fcos (I := I) (M := M) q y →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) (Work.Diff.C.fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, Work.Diff.C.HessBoundRegion (I := I) (M := M) cov c ε₁ (Work.Diff.C.fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (Work.Diff.C.fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < Work.Diff.C.fcos (I := I) (M := M) q y →
      Inner.inner ℝ (Work.Diff.C.rgrad (I := I) (M := M) (Work.Diff.C.fcos (I := I) (M := M) q) y)
        (Work.Diff.C.rgrad (I := I) (M := M) (Work.Diff.C.fcos (I := I) (M := M) q) y)
        = 1 - (Work.Diff.C.fcos (I := I) (M := M) q y) ^ 2)
    (hmod : ∀ {q : M} {v : TangentSpace I q}, ‖v‖ = 1 → ∀ {ρ : ℝ}, 0 < ρ →
      ρ ≤ Real.pi - Real.arccos (1 - c) → Real.sqrt ε₁ ≤ ρ →
      ∀ {Z : (t : ℝ) → TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))},
      (∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov
        (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) Z t) →
      Z 0 = 0 → Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z 0) v = 0 →
      ‖Z ρ‖ ≤ (Real.sin ρ + 25 * ε₁) * ‖Submission.JacobiGlobal.covAlong cov Z 0‖)
    {q : M} {ρ : ℝ} (hρ0 : 0 < ρ) (hρπ : ρ ≤ Real.pi - Real.arccos (1 - c))
    (hρe : Real.sqrt ε₁ ≤ ρ)
    {u w : TangentSpace I q} (hu : ‖u‖ = 1) (hw : Inner.inner ℝ u w = 0) :
    ‖(mfderiv (modelWithCornersSelf ℝ E) I
        (fun x : E => Submission.GlobalExp.GExp (cov := cov) hmet q
          (ρ • (show TangentSpace I q from x)))
        (show E from u)) (show E from w)‖
      ≤ (Real.sin ρ + 25 * ε₁) * ‖w‖ := by
  -- The parametrisation `Φ u = GExp q (ρ • u)` of the radius-`ρ` sphere, as a map on the model
  -- space `E`.
  set F : E → M := fun x : E => Submission.GlobalExp.GExp (cov := cov) hmet q
      (ρ • (show TangentSpace I q from x)) with hFdef
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    norm_num at hu
  -- ## The radial Jacobi field: the variation field of the family of rays
  -- `r ↦ GExp q (t • (u + r • w))` at `r = 0`.  Its value at `ρ` is the differential of `Φ`, and
  -- its covariant derivative at `0` is `w`.
  set Z : (t : ℝ) → TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) :=
      fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (u + r • w))) 0 with hZdef
  have hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov
      (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) Z t := by
    intro t
    rw [hZdef]
    exact Submission.RayJacobi.isJacobiAt_GExp_variation (cov := cov) hmet htor hu0 hu t
  have hZ0 : Z 0 = 0 := by
    rw [hZdef]
    exact Work.OddBound.longHomotopy.variation_zero_at_zero (cov := cov) hmet
  -- the initial covariant derivative is `w` (up to the base point `GExp q (0 • u)` vs `q`)
  have hA0 : Submission.JacobiGlobal.covAlong cov
      (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (u + r • w))) 0) 0 = w :=
    Work.OddBound.longHomotopy.covAlong_variation_zero (cov := cov) hmet htor hu0
  have hcov0 : Submission.JacobiGlobal.covAlong cov Z 0 = w := by
    have hgam : (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))
        = (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (u + (0 : ℝ) • w))) := by
      funext t
      congr 1
      rw [zero_smul, add_zero]
    have hVl : ∀ t : ℝ, (show E from Z t)
        = (show E from Submission.Geodesic.curveVelocity (I := I)
            (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (u + r • w))) 0) := by
      intro t
      rw [hZdef]
    exact (covAlong_congr_curve' (cov := cov)
      (γ₁ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))
      (γ₂ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (u + (0 : ℝ) • w)))
      hgam (V₁ := Z) (V₂ := fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (u + r • w))) 0) hVl 0).trans hA0
  have hpt : (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) 0 = q := by
    simp [Submission.GlobalExp.GExp_zero]
  have hnorm0 : ‖Submission.JacobiGlobal.covAlong cov Z 0‖ = ‖w‖ := by
    rw [hcov0]
    exact norm_congr_point' (I := I) hpt (show E from w)
  have horth : Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z 0) u = 0 := by
    rw [hcov0]
    rw [inner_congr_point' (I := I) hpt (show E from w) (show E from u)]
    rw [real_inner_comm]
    exact hw
  -- ## The modulus hypothesis, applied to the radial Jacobi field
  have hbound : ‖Z ρ‖ ≤ (Real.sin ρ + 25 * ε₁) * ‖Submission.JacobiGlobal.covAlong cov Z 0‖ :=
    hmod hu hρ0 hρπ hρe (Z := Z) hJ hZ0 horth
  -- ## `ⅆΦ(u)[w] = Z ρ`: both are the differential of `GExp q` at `ρ • u` in the direction `ρ • w`
  have hσ : HasDerivAt (fun r : ℝ => (show E from (u + r • w))) (show E from w) 0 := by
    have h1 : HasDerivAt (fun r : ℝ => r • w) w (0 : ℝ) := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
    have h2 : HasDerivAt (fun r : ℝ => u + r • w) w (0 : ℝ) := h1.const_add u
    simpa using h2
  have hF1 : MDifferentiableAt 𝓘(ℝ, E) I F ((fun r : ℝ => (show E from (u + r • w))) 0) := by
    have hinner : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ((⊤ : ENat) : WithTop ENat)
        (fun x : E => (ρ • x : E))
        ((fun r : ℝ => (show E from (u + r • w))) 0) := by
      rw [contMDiffAt_iff_contDiffAt]
      fun_prop
    have hG := Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet q
      (ρ • (show TangentSpace I q from ((fun r : ℝ => (show E from (u + r • w))) 0)))
    have hcomp := hG.comp ((fun r : ℝ => (show E from (u + r • w))) 0) hinner
    exact hcomp.mdifferentiableAt (by decide)
  have hcA := Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp (I := I)
    (f := F) (σ := fun r : ℝ => (show E from (u + r • w))) (σ' := fun _ : ℝ => (show E from w))
    (γ := fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • (u + r • w)))
    (t := 0) hσ hF1 (Filter.Eventually.of_forall fun r => rfl)
  have hmv : (mfderiv% F ((fun r : ℝ => (show E from (u + r • w))) 0)) (show E from w)
      = (mfderiv% F (show E from u)) (show E from w) := by
    rw [show (fun r : ℝ => (show E from (u + r • w))) 0 = (show E from u) from by
      simp only [zero_smul, add_zero]]
  have hZρ : Z ρ = Submission.Geodesic.curveVelocity (I := I)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • (u + r • w))) 0 := by
    rw [hZdef]
  have hval : (mfderiv (modelWithCornersSelf ℝ E) I F (show E from u)) (show E from w) = Z ρ :=
    (hcA.trans hmv).symm.trans hZρ.symm
  have hvalN : ‖(mfderiv (modelWithCornersSelf ℝ E) I F (show E from u))
      (show E from w)‖ = ‖Z ρ‖ :=
    congrArg (fun z => ‖z‖) hval
  -- ## Assembly
  change ‖(mfderiv (modelWithCornersSelf ℝ E) I F (show E from u)) (show E from w)‖
      ≤ (Real.sin ρ + 25 * ε₁) * ‖w‖
  rw [hvalN]
  rw [← hnorm0]
  exact hbound

end Work.Diff.C.RadialBound
