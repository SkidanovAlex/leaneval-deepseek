import Mathlib
import Submission.Work.Diff.C.geoCrux.Port.CoreStmts
import Submission.Work.Diff.C.geoCrux.Port.InjCore
import Submission.Work.Diff.C.geoCrux.Port.SharpInterfaces
import Submission.Work.Diff.C.geoCrux.RadialBase
import Submission.Work.Diff.C.geoCrux.RauchInputDefs
import Submission.Work.Diff.C.dmRadialBridge
import Submission.Work.Diff.C.JacobiLogDeriv
import Submission.Work.Diff.C.JacobiModulusRiccati
import Submission.Work.Diff.C.no_conjTime_le_arccos
import Submission.Work.Diff.C.isJacobiAt_add
import Submission.Work.Diff.C.JacobiUniqAux
import Submission.Work.Diff.C.far_sphere_size
import Submission.Work.OddBound.longHomotopy.gauss_pairing_fibre
import Submission.Work.OddBound.longHomotopy.covAlong_variation_zero
import Submission.Work.OddBound.polygon.isConjugateTime_comp_sub
import Submission.RayJacobi
import Submission.CurvatureSym
import Submission.GExpTranslate
import Submission.LensLoop
import Submission.ConjEnergy
import Submission.EnergyRayCover
import Submission.GExpRay
import Submission.GExpRayZero
import Submission.JacobiGlobal
import Submission.InjRadius

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two-centre core of the sharp radial modulus bound (self-contained development)

This file develops, from the *stable* library lemmas only, the machinery needed for
`Work.Diff.C.geoCrux.Port.TwoCentreCoreProp` (the two-centre inequality, the geometric core of the sharp
radial modulus bound):

* `fv` — the radial variation field of the family of rays out of a point, with the usual properties
  (linear in the direction, vanishing at `0`, covariant derivative `ξ` at `0`, orthogonal to the
  ray, Jacobi along the ray, Gauss pairing);
* `wronskianConst` — the constancy of the Wronskian of two Jacobi fields along a curve;
* `jacobiUniqSmooth` — uniqueness of a Jacobi field with prescribed data at one time.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic Submission.Jacobi Submission.Rauch Submission.JacobiVec
open Submission.ChartConnection Submission.RauchGlobal Submission.JacobiGlobal

namespace Work.Diff.C.geoCrux.Port

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-! ## 1. The radial variation field -/

/-- **The differential of the exponential map** at `σ • v`, as a continuous linear map `E → E`. -/
noncomputable def Jop (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (σ : ℝ) :
    E →L[ℝ] TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (σ • v)) :=
  mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet q w) (σ • v)

/-- **The radial variation field** of the family of rays out of `q`: the velocity at `0` of the curve
`r ↦ GExp q (σ • (v + r • ξ))`, an element of `T_{GExp q (σ • v)}M`. -/
noncomputable def fv (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q)
    (σ : ℝ) :=
  Submission.Geodesic.curveVelocity (I := I)
    (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • (v + r • ξ))) 0

/-- The variation field is the differential of the exponential map applied to `σ • ξ`. -/
lemma fv_eq_Jop (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) (σ : ℝ) :
    fv (cov := cov) hmet q v ξ σ = Jop (cov := cov) hmet q v σ (σ • ξ) :=
  Work.OddBound.longHomotopy.curveVelocity_GExp_smul_variation (cov := cov) hmet σ v ξ

/-- The variation field is the differential of the exponential map at `σ • v` applied to `σ • ξ`. -/
lemma fv_eq_mfderiv (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q)
    (σ : ℝ) :
    fv (cov := cov) hmet q v ξ σ
      = (mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet q w)
          (σ • v)) (σ • ξ) :=
  Work.OddBound.longHomotopy.curveVelocity_GExp_smul_variation (cov := cov) hmet σ v ξ

/-- The variation field is the velocity of the varied curve. -/
lemma fv_eq_vel (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) (σ : ℝ) :
    fv (cov := cov) hmet q v ξ σ
      = Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • (v + r • ξ))) 0 := rfl

/-- **Linearity** of the variation field in its direction (stated through the point of `σ • v`, so
that the two summands live in the same tangent space). -/
lemma fv_add (hmet : IsMetricCompatible cov) (q : M) (v ξ ξ' : TangentSpace I q) (σ : ℝ) :
    (show TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (σ • v)) from
        fv (cov := cov) hmet q v (ξ + ξ') σ)
      = (show TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (σ • v)) from
          fv (cov := cov) hmet q v ξ σ)
        + (show TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (σ • v)) from
            fv (cov := cov) hmet q v ξ' σ) := by
  simp only [fv_eq_Jop]
  rw [smul_add]
  exact map_add _ _ _

/-- **Homogeneity** of the variation field in its direction. -/
lemma fv_smul (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) (σ a : ℝ) :
    (show TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (σ • v)) from
        fv (cov := cov) hmet q v (a • ξ) σ)
      = a • (show TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (σ • v)) from
          fv (cov := cov) hmet q v ξ σ) := by
  simp only [fv_eq_Jop]
  rw [smul_comm]
  exact map_smul (Jop (cov := cov) hmet q v σ) a (σ • ξ)

/-- The variation field vanishes in the direction `ξ = 0`. -/
lemma fv_zero (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (σ : ℝ) :
    fv (cov := cov) hmet q v 0 σ = 0 := by
  rw [fv_eq_Jop]
  simp

/-- The variation field vanishes at `σ = 0`. -/
lemma fv_eq_zero_at_zero (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) :
    fv (cov := cov) hmet q v ξ 0 = 0 := by
  rw [fv_eq_Jop]
  simp

/-- The variation field is a Jacobi field along the ray. -/
lemma fv_isJacobiAt (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (q : M)
    {v : TangentSpace I q} (hv0 : v ≠ 0) (hv : ‖v‖ = 1) {ξ : TangentSpace I q} (σ : ℝ) :
    Submission.RauchGlobal.IsJacobiAt cov
      (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
      (fun t : ℝ => fv (cov := cov) hmet q v ξ t) σ :=
  Submission.RayJacobi.isJacobiAt_GExp_variation (cov := cov) hmet htor hv0 hv
    (η := ξ) σ

/-- The covariant derivative at `0` of the variation field is its direction. -/
lemma fv_covAlong_zero (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (q : M)
    {v : TangentSpace I q} (hv0 : v ≠ 0) (ξ : TangentSpace I q) :
    Submission.JacobiGlobal.covAlong cov
        (fun t : ℝ => fv (cov := cov) hmet q v ξ t) 0 = ξ :=
  Work.OddBound.longHomotopy.covAlong_variation_zero (cov := cov) hmet htor hv0
    (p := q) (u := v) (η := ξ)

/-- **The Gauss pairing**: `⟪Z_ξ(σ), γ'(σ)⟫ = σ ⟪ξ,v⟫`. -/
lemma fv_gauss (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (q : M)
    (v ξ : TangentSpace I q) (σ : ℝ) :
    Inner.inner ℝ (fv (cov := cov) hmet q v ξ σ)
        (Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) σ)
      = σ * Inner.inner ℝ ξ v :=
  Work.OddBound.longHomotopy.gauss_pairing_fibre (cov := cov) hmet htor
    (p := q) (v := v) (η := ξ) σ

/-! ## 2. Constancy of the Wronskian of two Jacobi fields -/

/-- **The Wronskian of two Jacobi fields is constant.** -/
theorem wronskianConst (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {J K : (t : ℝ) → TangentSpace I (γ t)}
    (hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ J t)
    (hK : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ K t) (t₀ t : ℝ) :
    Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t) (K t)
        - Inner.inner ℝ (J t) (Submission.JacobiGlobal.covAlong cov K t)
      = Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t₀) (K t₀)
        - Inner.inner ℝ (J t₀) (Submission.JacobiGlobal.covAlong cov K t₀) := by
  set F : ℝ → ℝ := fun s => Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J s) (K s)
    - Inner.inner ℝ (J s) (Submission.JacobiGlobal.covAlong cov K s) with hF
  have hderiv : ∀ s : ℝ, HasDerivAt F 0 s := by
    intro s
    have h1 := Work.Diff.C.jml_hasDerivAt_inner_covAlong_two (I := I) (M := M) (cov := cov)
      hmet htor hγ hJ hK hne s
    have h2 := Work.Diff.C.jml_hasDerivAt_inner_covAlong_two (I := I) (M := M) (cov := cov)
      hmet htor hγ hK hJ hne s
    have h2' : HasDerivAt
        (fun s : ℝ => Inner.inner ℝ (J s) (Submission.JacobiGlobal.covAlong cov K s))
        (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov K s)
            (Submission.JacobiGlobal.covAlong cov J s)
          - Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ s) (K s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)) (J s)) s := by
      simpa only [real_inner_comm] using h2
    have hsub := h1.sub h2'
    have hzero : Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J s)
          (Submission.JacobiGlobal.covAlong cov K s)
        - Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ s) (J s)
            (Submission.Geodesic.curveVelocity (I := I) γ s)
            (Submission.Geodesic.curveVelocity (I := I) γ s)) (K s)
        - (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov K s)
              (Submission.JacobiGlobal.covAlong cov J s)
          - Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ s) (K s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)) (J s)) = 0 := by
      have hsym := Submission.CurvatureSym.inner_curvVec_self_adjoint (cov := cov)
        (inferInstance : ContMDiffCovariantDerivative cov ∞) htor hmet (γ s) (J s)
        (Submission.Geodesic.curveVelocity (I := I) γ s) (K s)
      have hsym' : Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ s) (K s)
            (Submission.Geodesic.curveVelocity (I := I) γ s)
            (Submission.Geodesic.curveVelocity (I := I) γ s)) (J s)
          = Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ s) (J s)
            (Submission.Geodesic.curveVelocity (I := I) γ s)
            (Submission.Geodesic.curveVelocity (I := I) γ s)) (K s) := by
        calc Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ s) (K s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)) (J s)
            = Inner.inner ℝ (J s) (Submission.CurvatureVec.curvVec cov (γ s) (K s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)) := real_inner_comm _ _
          _ = Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ s) (J s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)) (K s) := hsym.symm
      have hcomm : Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov K s)
            (Submission.JacobiGlobal.covAlong cov J s)
          = Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J s)
            (Submission.JacobiGlobal.covAlong cov K s) := real_inner_comm _ _
      rw [hcomm, hsym']
      ring
    exact hsub.congr_deriv hzero
  have hdiff : Differentiable ℝ F := fun s => (hderiv s).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun s => (hderiv s).deriv)
  exact hconst t t₀

/-! ## 3. Uniqueness of a Jacobi field with prescribed data at one time (smooth level) -/

/-- `chartCovDeriv` is additively negative in the field. -/
lemma chartCovDeriv_neg_aux {x₀ : M} (u w y : ℝ → E) (s : ℝ) :
    chartCovDeriv cov x₀ u w (fun σ : ℝ ↦ -y σ) s
      = -(chartCovDeriv cov x₀ u w y s) := by
  have hd : deriv (fun σ : ℝ ↦ -y σ) s = -deriv y s := deriv.neg
  simp only [chartCovDeriv, hd, map_neg, neg_add]

/-- **`IsJacobiAt` is closed under negation of the field.** -/
lemma isJacobiAt_neg_aux {γ : ℝ → M} {Z : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hZ : Submission.RauchGlobal.IsJacobiAt cov γ Z t) :
    Submission.RauchGlobal.IsJacobiAt cov γ (fun s : ℝ ↦ -Z s) t := by
  obtain ⟨x₀, u, w, y, hTgt, huD, hγeq, hyF, hunit, hyd, hzd, hjac⟩ := hZ
  have hfe : chartCovDeriv cov x₀ u w (fun σ : ℝ ↦ -y σ)
      = fun σ : ℝ ↦ -(chartCovDeriv cov x₀ u w y σ) := by
    funext σ
    exact chartCovDeriv_neg_aux u w y σ
  refine ⟨x₀, u, w, fun s : ℝ ↦ -y s, hTgt, huD, hγeq, ?_, hunit, ?_, ?_, ?_⟩
  · filter_upwards [hyF] with s hs
    rw [frameVector_neg, hs]
  · filter_upwards [hyd] with s hs
    exact hs.neg.congr_deriv (deriv.neg (f := y) (x := s)).symm
  · filter_upwards [hzd] with s hs
    rw [hfe]
    exact hs.neg.congr_deriv (deriv.neg (f := chartCovDeriv cov x₀ u w y) (x := s)).symm
  · filter_upwards [hjac, hTgt] with s hj htg
    have hp : (extChartAt I x₀).symm (u s) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) htg
    have hneg : chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w (fun σ : ℝ ↦ -y σ)) s
        = -(chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) s) := by
      rw [hfe, chartCovDeriv_neg_aux u w (chartCovDeriv cov x₀ u w y) s]
    have hcurv : chartCurv cov x₀ ((extChartAt I x₀).symm (u s)) (-y s) (w s)
        = -(chartCurv cov x₀ ((extChartAt I x₀).symm (u s)) (y s) (w s)) := by
      rw [← neg_one_smul ℝ (y s),
        chartCurv_smul_fst (cov := cov) x₀ ((extChartAt I x₀).symm (u s)) hp (-1) (y s) (w s),
        neg_one_smul]
    rw [hneg, hcurv, ← neg_add, hj, neg_zero]

/-- **`IsJacobiAt` is closed under subtraction of fields** (germ form). -/
lemma isJacobiAt_sub_aux (htor : cov.torsion = 0) {γ : ℝ → M}
    {J Z : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hJ : Submission.RauchGlobal.IsJacobiAt cov γ J t)
    (hZ : Submission.RauchGlobal.IsJacobiAt cov γ Z t) :
    Submission.RauchGlobal.IsJacobiAt cov γ (fun s : ℝ ↦ J s - Z s) t := by
  have h := isJacobiAt_add (cov := cov) htor hJ (isJacobiAt_neg_aux (cov := cov) hZ)
  convert h using 1
  funext s
  exact sub_eq_add_neg _ _

/-- **Uniqueness of a Jacobi field from its data at one time** (smooth level). -/
theorem jacobiUniqSmooth : Work.Diff.C.geoCrux.Port.JacobiUniqSmooth := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBd iNt iCS cov iCd
    htor γ hγ hne J Z hJ hZ t₀ hv hd t
  have hW : ∀ s : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ (fun r : ℝ ↦ J r - Z r) s :=
    fun s ↦ isJacobiAt_sub_aux (cov := cov) htor (hJ s) (hZ s)
  have h0 : (fun r : ℝ ↦ J r - Z r) t₀ = 0 := by
    show J t₀ - Z t₀ = 0
    rw [hv, sub_self]
  have hd0 : Submission.JacobiGlobal.covAlong cov (fun r : ℝ ↦ J r - Z r) t₀ = 0 := by
    rw [Work.Diff.C.covAlong_sub (cov := cov) htor hγ hJ hZ t₀, hd, sub_self]
  have hzero := Work.Diff.C.eq_of_dual_zero (cov := cov) htor hγ hne hW h0 hd0 t
  exact sub_eq_zero.mp hzero

end Work.Diff.C.geoCrux.Port
