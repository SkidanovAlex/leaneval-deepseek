import Mathlib
import Submission.Work.Diff.C.ShapeAux.Kit
import Submission.Work.Diff.C.ShapeAux.gauss_pairing_second_deriv
import Submission.Work.Diff.C.ShapeAux.deriv_deriv_comp_curve
import Submission.Work.Diff.C.ShapeAux.norm_add_smul_deriv_deriv

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.GlobalExp Submission.Geodesic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-!
# The shape operator as the covariant derivative of the radial Jacobi field

For the family of rays `F (s,t) = GExp p (t • (u + s • η))` out of `p` (with `⟪u,u⟫ = 1`,
`⟪u,η⟫ = 0`), let `Z t = ∂_s F (s,t)|_{s=0}` be the variation field (a Jacobi field along the ray
with `Z 0 = 0`).  This file proves, **without any curvature hypothesis**,

  `⟪∇_t Z d, Z d⟫ = rhess (rdist p) (GExp p (d • u)) (Z d) (Z d)`,

i.e. the covariant derivative of the variation field equals the Hessian of the distance function
(the *shape operator* of the geodesic sphere of radius `d` around `p`) applied to `Z d`.  This is the
`hbridge` input of `Work.Diff.C.jld_modulus_le_sin` (the Riccati/Sturm comparison for the modulus),
which is the engine behind the geodesic-sphere-size bound.

Route: `Work.Diff.C.ShapeAux.gauss_pairing_second_deriv` computes

  `⟪∇_s ∂_s F, γ'⟫ + ⟪∇_t Z, Z⟫ = d ⟪η,η⟫`

(the second variation of the length of the radial family), and the second-order chain rule
`Work.Diff.C.ShapeAux.deriv_deriv_comp_curve` applied to `rdist p` along the curve
`s ↦ GExp p (d • (u + s • η))` computes

  `⟪∇_s ∂_s F, ∇ (rdist p)⟫ = (d²/ds²) (rdist p ∘ c) - rhess (rdist p) (Z d, Z d)`,

with `(d²/ds²)(rdist p ∘ c) = d ⟪η,η⟫` by `Work.Diff.C.ShapeAux.norm_add_smul_deriv_deriv` (the curve
stays radial: `rdist p (GExp p (d • (u + s • η))) = ‖d • (u + s • η)‖` for `s` near `0`).  Comparing
the two expressions (and using `∇ (rdist p) (GExp p (d•u)) = γ' d`) gives the claim. -/

/-- **The radial variation field realises the shape operator.** -/
theorem dmRadialBridge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
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
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {d : ℝ} (hd : 0 < d) {u η : TangentSpace I p}
    (hu : Inner.inner ℝ u u = 1) (horth : Inner.inner ℝ u η = 0)
    (hsm : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
      (fun z : M ↦ rdist (I := I) (M := M) p z)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
    (hrgrad : rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))
      = Submission.Geodesic.curveVelocity (I := I)
          (fun t : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) d)
    (hcsm : ContMDiff (modelWithCornersSelf ℝ ℝ) I ((⊤ : ENat) : WithTop ENat)
      (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η))))
    (hne : Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η))) 0 ≠ 0)
    (hminW : ∀ᶠ s in 𝓝 (0 : ℝ),
      rdist (I := I) (M := M) p
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η)))
        = ‖d • (u + s • η)‖) :
    Inner.inner ℝ
        (Submission.JacobiGlobal.covAlong cov
          (γ := fun t : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (t • u))
          (fun t : ℝ ↦ Submission.Geodesic.curveVelocity (I := I)
            (fun r : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0) d)
        (Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))
          (Submission.Geodesic.curveVelocity (I := I)
            (fun r : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0)
          (Submission.Geodesic.curveVelocity (I := I)
            (fun r : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0) := by
  classical
  -- `‖u‖ = 1`
  have hnu : ‖u‖ = 1 := by
    have h : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hu
    nlinarith [norm_nonneg u]
  -- local notation
  let c : ℝ → M := fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η))
  let Z : (t : ℝ) → TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) :=
    fun t : ℝ ↦ Submission.Geodesic.curveVelocity (I := I)
      (fun r : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0
  let gam : ℝ → M := fun t : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)
  let V : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) :=
    Submission.Geodesic.curveVelocity (I := I)
      (fun r : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0
  let W : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) :=
    Submission.Geodesic.curveVelocity (I := I) gam d
  let A : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) :=
    Submission.JacobiGlobal.covAlong cov (γ := c)
      (fun s : ℝ ↦ Submission.Geodesic.curveVelocity (I := I) c s) 0
  let B : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) :=
    Submission.JacobiGlobal.covAlong cov (γ := gam) (fun t : ℝ ↦ Z t) d
  -- ## 1. the Gauss pairing identity of the radial family
  have hgp := Work.Diff.C.ShapeAux.gauss_pairing_second_deriv (cov := cov) (p := p) hmet htor
    (d := d) hd (u := u) (η := η) hnu hne
  rw [zero_smul, add_zero] at hgp
  -- the endpoint of `c` is the point of the statement
  have hc0 : c 0 = Submission.GlobalExp.GExp (cov := cov) hmet p (d • u) := by
    simp only [c, zero_smul, add_zero]
  -- ## 2. the second-order chain rule for `rdist p ∘ c`
  have hsm' : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
      (fun z : M ↦ rdist (I := I) (M := M) p z) (c 0) := by
    simpa only [c, zero_smul, add_zero] using hsm
  have hcr := Work.Diff.C.ShapeAux.deriv_deriv_comp_curve (cov := cov) hmet htor
    (f := fun z : M ↦ rdist (I := I) (M := M) p z) (x := c 0) (c := c)
    (hf := hsm') (hc0 := rfl) (hc := hcsm) (hne := by simpa only [c] using hne)
  -- ## 3. the same derivative, computed from the radial identity
  have hfun : (fun s : ℝ ↦ ‖d • (u + s • η)‖)
      = fun s : ℝ ↦ ‖(d • u) + s • (d • η)‖ := by
    funext s
    rw [smul_add, smul_smul, smul_smul, mul_comm s d]
  have hev : (fun s : ℝ ↦ rdist (I := I) (M := M) p (c s))
      =ᶠ[𝓝 (0 : ℝ)] (fun s : ℝ ↦ ‖(d • u) + s • (d • η)‖) := by
    filter_upwards [hminW] with s hs
    exact hs.trans (congrFun hfun s)
  obtain ⟨-, hd2⟩ := Work.Diff.C.ShapeAux.norm_add_smul_deriv_deriv
    (a := d • u) (b := d • η) (by
      simp only [ne_eq, smul_eq_zero, not_or]
      exact ⟨ne_of_gt hd, by
        intro h
        rw [h] at hnu
        norm_num at hnu⟩)
  have hder : deriv (fun s : ℝ ↦ rdist (I := I) (M := M) p (c s))
      =ᶠ[𝓝 (0 : ℝ)] deriv (fun s : ℝ ↦ ‖(d • u) + s • (d • η)‖) := hev.deriv
  have hval2 : HasDerivAt (deriv (fun s : ℝ ↦ rdist (I := I) (M := M) p (c s)))
      ((‖d • u‖ ^ 2 * ‖d • η‖ ^ 2 - (Inner.inner ℝ (d • u) (d • η)) ^ 2) / ‖d • u‖ ^ 3) 0 :=
    hd2.congr_of_eventuallyEq hder
  -- ## 4. the value of the right-hand side
  have hRHS : (‖d • u‖ ^ 2 * ‖d • η‖ ^ 2 - (Inner.inner ℝ (d • u) (d • η)) ^ 2) / ‖d • u‖ ^ 3
      = d * Inner.inner ℝ η η := by
    have hdu : ‖d • u‖ = d := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd, hnu, mul_one]
    have hde : ‖d • η‖ = d * ‖η‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    have hinn : Inner.inner ℝ (d • u) (d • η) = 0 := by
      rw [real_inner_smul_left, real_inner_smul_right, horth, mul_zero, mul_zero]
    have heta : Inner.inner ℝ η η = ‖η‖ ^ 2 := real_inner_self_eq_norm_sq η
    rw [hdu, hde, hinn, heta]
    have hdne : d ≠ 0 := ne_of_gt hd
    field_simp
    ring
  -- ## 5. assembly
  have hsymm : Inner.inner ℝ (rgrad (I := I) (M := M)
      (fun z : M ↦ rdist (I := I) (M := M) p z)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) A = Inner.inner ℝ A W := by
    rw [hrgrad]
    exact (real_inner_comm W A).symm
  have hconcl : rhess cov (fun z : M ↦ rdist (I := I) (M := M) p z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) V V
      = Inner.inner ℝ B V := by
    have h1 : rhess cov (fun z : M ↦ rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) V V
        + Inner.inner ℝ A W = d * Inner.inner ℝ η η := by
      have h2 : rhess cov (fun z : M ↦ rdist (I := I) (M := M) p z) (c 0) V V
          + Inner.inner ℝ (rgrad (I := I) (M := M)
              (fun z : M ↦ rdist (I := I) (M := M) p z) (c 0)) A
          = (‖d • u‖ ^ 2 * ‖d • η‖ ^ 2
              - (Inner.inner ℝ (d • u) (d • η)) ^ 2) / ‖d • u‖ ^ 3 :=
        hcr.deriv.symm.trans hval2.deriv
      rw [hRHS] at h2
      rw [hc0] at h2
      simpa only [hsymm] using h2
    linarith [hgp, h1]
  -- ## 6. the goal
  exact hconcl.symm

/-- **The radial variation field is orthogonal to the radial direction.**  For the variation field
`Z t = ∂_s GExp p (t • (u + s • η))|_0` of the family of rays out of `p` (`⟪u,u⟫ = 1`, `⟪u,η⟫ = 0`),

  `⟪Z d, γ' d⟫ = 0`   (`γ' d = ∂_t GExp p (t • u)|_d`).

This is `Work.Diff.C.ShapeAux.gauss_pairing_scalar` at `s = 0` (the Gauss lemma for the family of
rays).  With `Work.Diff.C.dmRadialBridge` it supplies the `horth` input of
`Work.Diff.C.jld_modulus_le_sin` (the geodesic-sphere-size comparison). -/
theorem dmRadialOrthogonal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
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
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {d : ℝ} {u η : TangentSpace I p}
    (hu : Inner.inner ℝ u u = 1) (horth : Inner.inner ℝ u η = 0) :
    Inner.inner ℝ
        (show TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) from
          Submission.Geodesic.curveVelocity (I := I)
            (fun r : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0)
        (show TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) from
          Submission.Geodesic.curveVelocity (I := I)
            (fun t : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) d) = 0 := by
  have h := Work.Diff.C.ShapeAux.gauss_pairing_scalar (cov := cov) (p := p) hmet htor d (u := u)
    (η := η) 0
  rw [zero_smul, add_zero] at h
  have h2 : Inner.inner ℝ η u = 0 := (real_inner_comm η u).symm.trans horth
  simpa only [h2, mul_zero] using h

end Work.Diff.C
