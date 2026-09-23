import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.IndexIntrinsic2
import Submission.JacobiCoordsEq
import Submission.GeodesicExtend
import Submission.CurveField
import Submission.Variation
import Submission.ChartIndep

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-- The curvature vector `R(u,v)v` has vanishing square: `⟪R(u,v)v, v⟫ = 0`, by the
skew-symmetry of the curvature in its last two arguments. -/
lemma inner_curvVec_last_eq_zero (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (x : M) (u v : TangentSpace I x) :
    Inner.inner ℝ (Submission.CurvatureVec.curvVec cov x u v v) v = 0 := by
  have h := Submission.CurvatureVec.inner_curvVec_skew cov
    ‹CovariantDerivative.ContMDiffCovariantDerivative cov ∞› hmet x u v v v
  have h2 := real_inner_comm (Submission.CurvatureVec.curvVec cov x u v v) v
  linarith

/-- **First order: the pairing of a Jacobi field with the velocity.**  Along a `C^∞` geodesic `γ`
with non-vanishing velocity and a field `J` which is a Jacobi field near every time, the derivative
of `t ↦ ⟪J t, γ'(t)⟫` at `t` is `⟪∇_{γ'}J(t), γ'(t)⟫`. -/
lemma hasDerivAt_inner_jacobi_velocity
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    (hJ : ∀ s, Submission.RauchGlobal.IsJacobiAt cov γ J s)
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ s, curveVelocity (I := I) γ s ≠ 0)
    (hgeo : ∀ s, IsGeodesicAt cov γ s) :
    ∀ t : ℝ,
      HasDerivAt (fun s => Inner.inner ℝ (J s) (curveVelocity (I := I) γ s))
        (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t)
          (curveVelocity (I := I) γ t)) t := by
  intro t
  have hγOn : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)) := hγ.contMDiffOn
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (hγ.contMDiffAt).mdifferentiableAt (by simp)
  have hVsm : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ J t :=
    Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJ hγOn
  obtain ⟨𝒱, h𝒱sm, h𝒱ev⟩ :=
    Submission.JacobiGlobal.exists_section_of_smoothAlongAt (I := I) hγOn (hne t) hVsm
  obtain ⟨𝒲, h𝒲sm, h𝒲ev⟩ :=
    Submission.CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity (I := I)
      (V := Ioo (t - 1) (t + 1)) isOpen_Ioo ⟨by linarith, by linarith⟩ hγOn (hne t)
  have hmain := Submission.Variation.hasDerivAt_inner_sections (cov := cov) hmet h𝒱sm h𝒲sm hγmd
  have hcovW : cov 𝒲 (γ t) (curveVelocity (I := I) γ t) = 0 := hgeo t 𝒲 h𝒲sm h𝒲ev
  have hcovV : cov 𝒱 (γ t) (curveVelocity (I := I) γ t)
      = Submission.JacobiGlobal.covAlong cov J t :=
    (Submission.JacobiGlobal.covAlong_eq_cov (cov := cov) htor hγOn (hne t) hVsm h𝒱sm h𝒱ev).symm
  have hval : Inner.inner ℝ (cov 𝒱 (γ t) (curveVelocity (I := I) γ t)) (𝒲 (γ t))
      + Inner.inner ℝ (𝒱 (γ t)) (cov 𝒲 (γ t) (curveVelocity (I := I) γ t))
      = Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t) (curveVelocity (I := I) γ t) := by
    rw [hcovV, hcovW, inner_zero_right, add_zero, Filter.Eventually.self_of_nhds h𝒲ev]
  have hev : (fun s => Inner.inner ℝ (𝒱 (γ s)) (𝒲 (γ s)))
      =ᶠ[𝓝 t] (fun s => Inner.inner ℝ (J s) (curveVelocity (I := I) γ s)) := by
    filter_upwards [h𝒱ev, h𝒲ev] with s h1 h2
    rw [h1, h2]
  exact (hmain.congr_deriv hval).congr_of_eventuallyEq hev.symm

/-- **Second order: the pairing of `∇_{γ'}J` with the velocity is constant.**  Along a `C^∞`
geodesic `γ` with non-vanishing velocity and a Jacobi field `J`, the derivative of
`t ↦ ⟪∇_{γ'}J(t), γ'(t)⟫` vanishes identically.  The proof is the pointwise Jacobi identity: the
derivative of that pairing is `⟪∇_{γ'}∇_{γ'}J, γ'⟫ = -⟪R(γ',J)γ', γ'⟫ = 0`. -/
lemma hasDerivAt_inner_covAlong_velocity
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    (hJ : ∀ s, Submission.RauchGlobal.IsJacobiAt cov γ J s)
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ s, curveVelocity (I := I) γ s ≠ 0)
    (hgeo : ∀ s, IsGeodesicAt cov γ s) :
    ∀ t : ℝ,
      HasDerivAt (fun s => Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J s)
        (curveVelocity (I := I) γ s)) 0 t := by
  intro t
  obtain ⟨x₀, η, hηpos, hηle, hsrcIcc, hcdu, hcdy, hframe, hjacIcc⟩ :=
    Submission.JacobiCoordsEq.exists_chartCoords_contDiffOn_eq (cov := cov) htor (γ := γ) (J := J)
      (s := t) (ε := 1) one_pos (hγ.contMDiffOn) (hJ t)
  set u : ℝ → E := Submission.IntrinsicVariation.chartCoord (I := I) x₀ γ with hudef
  set y : ℝ → E := Submission.JacobiCoords.chartCoords (I := I) x₀ γ J with hydef
  have hUsub : Ioo (t - η) (t + η) ⊆ Icc (t - η) (t + η) := fun s hs => ⟨hs.1.le, hs.2.le⟩
  have hUtgt : Ioo (t - η) (t + η) ⊆ Ioo (t - 1) (t + 1) := fun s hs =>
    ⟨by linarith [hs.1, hηle], by linarith [hs.2, hηle]⟩
  have htU : t ∈ Ioo (t - η) (t + η) := ⟨by linarith, by linarith⟩
  have hUopen : IsOpen (Ioo (t - η) (t + η)) := isOpen_Ioo
  have hUnhds : Ioo (t - η) (t + η) ∈ 𝓝 t := Ioo_mem_nhds htU.1 htU.2
  have hcduO : ContDiffOn ℝ ∞ u (Ioo (t - η) (t + η)) := hcdu.mono hUsub
  have hcdyO : ContDiffOn ℝ ∞ y (Ioo (t - η) (t + η)) := hcdy.mono hUsub
  have hcduO' : ContDiffOn ℝ ∞ (deriv u) (Ioo (t - η) (t + η)) :=
    hcduO.deriv_of_isOpen hUopen (le_of_eq (by simp))
  have hcdyO' : ContDiffOn ℝ ∞ (deriv y) (Ioo (t - η) (t + η)) :=
    hcdyO.deriv_of_isOpen hUopen (le_of_eq (by simp))
  have hdu : ∀ s ∈ Ioo (t - η) (t + η), HasDerivAt u (deriv u s) s := fun s hs =>
    (Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen hs hcduO).self_of_nhds
  have hdy : ∀ s ∈ Ioo (t - η) (t + η), HasDerivAt y (deriv y s) s := fun s hs =>
    (Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen hs hcdyO).self_of_nhds
  have hduEvAt : ∀ s ∈ Ioo (t - η) (t + η), ∀ᶠ r in 𝓝 s, HasDerivAt u (deriv u r) r := fun s hs =>
    Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) hdu
  have hdyEvAt : ∀ s ∈ Ioo (t - η) (t + η), ∀ᶠ r in 𝓝 s, HasDerivAt y (deriv y r) r := fun s hs =>
    Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) hdy
  have hdu_ev : ∀ᶠ s in 𝓝 t, HasDerivAt u (deriv u s) s :=
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen htU hcduO
  have hddu : HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    (Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen htU hcduO').self_of_nhds
  have hddy : HasDerivAt (deriv y) (deriv (deriv y) t) t :=
    (Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen htU hcdyO').self_of_nhds
  have hsrcU : ∀ s ∈ Ioo (t - η) (t + η), γ s ∈ (chartAt H x₀).source :=
    fun s hs => hsrcIcc s (hUsub hs)
  have hsrcEv : ∀ s ∈ Ioo (t - η) (t + η), ∀ᶠ r in 𝓝 s, γ r ∈ (chartAt H x₀).source := fun s hs =>
    Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) hsrcU
  have hutgtAt : ∀ s ∈ Ioo (t - η) (t + η), u s ∈ (extChartAt I x₀).target := by
    intro s hs
    exact (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hsrcU s hs)
  have huTgtEv : ∀ s ∈ Ioo (t - η) (t + η), ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target := fun s hs =>
    Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) hutgtAt
  have hγeqAt : ∀ s ∈ Ioo (t - η) (t + η), γ =ᶠ[𝓝 s] fun r => (extChartAt I x₀).symm (u r) := by
    intro s hs
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    rw [hudef]
    exact (PartialEquiv.left_inv (extChartAt I x₀)
      (by rw [extChartAt_source]; exact hsrcU r hr)).symm
  have hframeAt : ∀ s ∈ Ioo (t - η) (t + η), frameVector (I := I) x₀ (γ s) (y s) = J s := by
    intro s hs
    rw [hydef]
    exact hframe s (hUsub hs)
  have hframeEv : ∀ s ∈ Ioo (t - η) (t + η),
      ∀ᶠ r in 𝓝 s, frameVector (I := I) x₀ (γ r) (y r) = J r := fun s hs =>
    Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) hframeAt
  have hgeoChart : ∀ s ∈ Ioo (t - η) (t + η),
      HasDerivAt (deriv u) (chartGeodesicVectorField cov x₀ (u s, deriv u s)) s := by
    intro s hs
    exact Submission.GeodesicExtend.hasDerivAt_deriv_chartCurve_of_isGeodesicAt (cov := cov)
      (x₀ := x₀) (γ := γ) (V := Ioo (t - η) (t + η)) hUopen hs (hγ.contMDiffOn.mono hUtgt)
      (hsrcU s hs) (hgeo s) (hne s)
  have hDtQzeroAt : ∀ s ∈ Ioo (t - η) (t + η),
      Submission.BonnetMyers.DtQ cov x₀ u (deriv u) (deriv u) (deriv (deriv u)) s = 0 := by
    intro s hs
    have h1 : Submission.BonnetMyers.DtQ cov x₀ u (deriv u) (deriv u) (deriv (deriv u)) s
        = deriv (deriv u) s + Submission.ChartCurv.chrB cov x₀ ((extChartAt I x₀).symm (u s))
            (deriv u s) (deriv u s) := by
      simp only [Submission.BonnetMyers.DtQ, Submission.SecondVariation.covDsP,
        Submission.SecondVariation.fam, Submission.SecondVariation.famP, zero_smul, add_zero]
    rw [h1, (hgeoChart s hs).deriv]
    simp only [chartGeodesicVectorField, Submission.ChartCurv.chrB_apply, neg_add_cancel]
  have hZev : ∀ᶠ s in 𝓝 t, Submission.JacobiGlobal.covAlong cov J s
      = frameVector (I := I) x₀ (γ s)
        (Submission.BonnetMyers.DtQ cov x₀ u y (deriv u) (deriv y) s) := by
    refine Filter.eventually_of_mem hUnhds (fun s hs => ?_)
    have hVsm : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ J s :=
      Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJ hγ.contMDiffOn
    exact Submission.JacobiGlobal.covAlong_eq_chart (cov := cov) htor (γ := γ) (V := J) (t := s)
      hγ.contMDiffOn (hne s) hVsm (x₀ := x₀) (u := u) (w := deriv u) (y := y) (y' := deriv y)
      (hsrcU s hs) (hsrcEv s hs) (huTgtEv s hs) (hγeqAt s hs) (hduEvAt s hs) (hframeEv s hs)
      (hdyEvAt s hs)
  have hWhEv : ∀ᶠ s in 𝓝 t, curveVelocity (I := I) γ s
      = frameVector (I := I) x₀ (γ s) (deriv u s) := by
    refine Filter.eventually_of_mem hUnhds (fun s hs => ?_)
    exact (Submission.ChartIndep.frameVector_chartVel_eq_curveVelocity (I := I)
      (hsrcU s hs) (huTgtEv s hs) (hγeqAt s hs) (hduEvAt s hs)
      ((hγ.contMDiffAt).mdifferentiableAt (by simp))).symm
  have hYev : ∀ᶠ s in 𝓝 t, (0 : TangentSpace I (γ s))
      = frameVector (I := I) x₀ (γ s)
        (Submission.BonnetMyers.DtQ cov x₀ u (deriv u) (deriv u) (deriv (deriv u)) s) := by
    refine Filter.eventually_of_mem hUnhds (fun s hs => ?_)
    rw [hDtQzeroAt s hs]
    simp only [frameVector]
    rw [map_zero]
  have hjac_t : Submission.BonnetMyers.DtDsP cov x₀ u y (deriv u) (deriv y) t
      + Submission.Rauch.chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (deriv u t) = 0 :=
    hjacIcc t ⟨htU.1.le, htU.2.le⟩
  have hV_ev : ∀ᶠ s in 𝓝 t, J s = frameVector (I := I) x₀ (γ s) (y s) := by
    refine Filter.eventually_of_mem hUnhds (fun s hs => ?_)
    exact (hframeAt s hs).symm
  have hmain := Submission.IndexIntrinsic2.hasDerivAt_inner_bilAlong (cov := cov) hmet htor x₀
    (γ := γ) (V := J) (Z := Submission.JacobiGlobal.covAlong cov J)
    (W := fun s => curveVelocity (I := I) γ s) (Y := fun s => (0 : TangentSpace I (γ s)))
    (u := u) (w := deriv u) (w' := deriv (deriv u))
    (J := y) (J' := deriv y) (J'' := deriv (deriv y))
    (Wc := deriv u) (Wc' := deriv (deriv u)) (t := t)
    (hsrcU t htU) (huTgtEv t htU) (hγeqAt t htU) hdu_ev
    ((hγ.contMDiffAt).mdifferentiableAt (by simp)) hddu (hdy t htU) hddy hjac_t
    hV_ev hZev hddu hWhEv hYev
  have hbil : Submission.IndexIntrinsic2.bilAlong (cov := cov) γ J
      (fun s => curveVelocity (I := I) γ s)
      (Submission.JacobiGlobal.covAlong cov J) (fun s => (0 : TangentSpace I (γ s))) t = 0 := by
    simp only [Submission.IndexIntrinsic2.bilAlong, inner_zero_right, zero_sub, neg_eq_zero]
    exact inner_curvVec_last_eq_zero hmet (γ t) (J t) (curveVelocity (I := I) γ t)
  exact hmain.congr_deriv hbil

theorem pairing_affine_of_jacobi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    (hJ : ∀ s, Submission.RauchGlobal.IsJacobiAt cov γ J s)
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ s, Submission.Geodesic.curveVelocity (I := I) γ s ≠ 0)
    (hgeo : ∀ s, Submission.Geodesic.IsGeodesicAt cov γ s) :
    ∀ t : ℝ,
      Inner.inner ℝ (J t) (Submission.Geodesic.curveVelocity (I := I) γ t)
        = Inner.inner ℝ (J 0) (Submission.Geodesic.curveVelocity (I := I) γ 0)
          + t * Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J 0)
              (Submission.Geodesic.curveVelocity (I := I) γ 0) := by
  have hderiv1 := hasDerivAt_inner_jacobi_velocity (cov := cov) hmet htor hJ hγ hne hgeo
  have hderiv2 := hasDerivAt_inner_covAlong_velocity (cov := cov) hmet htor hJ hγ hne hgeo
  have hBconst : ∀ s : ℝ,
      Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J s)
          (Submission.Geodesic.curveVelocity (I := I) γ s)
        = Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J 0)
            (Submission.Geodesic.curveVelocity (I := I) γ 0) := by
    intro s
    refine is_const_of_deriv_eq_zero
      (f := fun r : ℝ => Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J r)
        (Submission.Geodesic.curveVelocity (I := I) γ r))
      (fun x => (hderiv2 x).differentiableAt) (fun x => (hderiv2 x).deriv) s 0
  intro t
  have hG : ∀ x : ℝ, HasDerivAt (fun s : ℝ =>
      Inner.inner ℝ (J s) (Submission.Geodesic.curveVelocity (I := I) γ s)
        - s * Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J 0)
            (Submission.Geodesic.curveVelocity (I := I) γ 0)) 0 x := by
    intro x
    have h2 : HasDerivAt (fun s : ℝ => s * Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J 0)
        (Submission.Geodesic.curveVelocity (I := I) γ 0))
        (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J 0)
          (Submission.Geodesic.curveVelocity (I := I) γ 0)) x := by
      simpa using (hasDerivAt_id x).mul_const
        (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J 0)
          (Submission.Geodesic.curveVelocity (I := I) γ 0))
    have h3 := (hderiv1 x).sub h2
    have hv : Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J x)
          (Submission.Geodesic.curveVelocity (I := I) γ x)
        - Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J 0)
            (Submission.Geodesic.curveVelocity (I := I) γ 0) = 0 := by
      rw [hBconst x, sub_self]
    have h4 := h3.congr_deriv hv
    exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => by rw [Pi.sub_apply]))
  have hconst := is_const_of_deriv_eq_zero
    (f := fun s : ℝ => Inner.inner ℝ (J s) (Submission.Geodesic.curveVelocity (I := I) γ s)
        - s * Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J 0)
            (Submission.Geodesic.curveVelocity (I := I) γ 0))
    (fun x => (hG x).differentiableAt) (fun x => (hG x).deriv) t 0
  have hconst' : Inner.inner ℝ (J t) (Submission.Geodesic.curveVelocity (I := I) γ t)
      - t * Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J 0)
          (Submission.Geodesic.curveVelocity (I := I) γ 0)
      = Inner.inner ℝ (J 0) (Submission.Geodesic.curveVelocity (I := I) γ 0) := by
    simpa using hconst
  linarith [hconst']

end Work.OddBound.longHomotopy
