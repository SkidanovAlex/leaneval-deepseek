import Submission.FlowJacobiGen
import Submission.GExpRayZero
import Submission.GExpSmooth
import Submission.RauchGlobal
import Submission.RayChart

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Commons.Analysis.Calculus
open Submission.Geodesic
open Submission.GlobalExp
open Submission.GExpSmooth
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.JacobiTensor
open Submission.Rauch
open Submission.RauchUpper
open Submission.SecondVariation
open Submission.SecondVar2
open Submission.FlowJacobi
open Submission.VariationJacobi
open Submission.RauchGlobal
open Submission.GeodesicExtend
open Submission.Jacobi
open Submission.FlowJacobiGen

namespace Submission.RayJacobi

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Joint smoothness of the two-parameter family of rays** `(σ, r) ↦ GExp p (σ • (u + r • η))`. -/
theorem contMDiffAt_GExp_family (hmet : IsMetricCompatible cov)
    {p : M} {u η : TangentSpace I p} (σ ρ : ℝ) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun q : ℝ × ℝ => GExp (cov := cov) hmet p (q.1 • (u + q.2 • η))) (σ, ρ) := by
  have hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
      (fun q : ℝ × ℝ => (show E from (q.1 • (u + q.2 • η)))) (σ, ρ) := by
    rw [contMDiffAt_iff_contDiffAt]
    fun_prop
  have hg := Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p (σ • (u + ρ • η))
  have hcomp := hg.comp (σ, ρ) hF
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards with q
  rfl

/-- **A product box on which the family stays in a fixed chart** (the chart centred at `γ t₀`). -/
theorem exists_window_GExp_family (hmet : IsMetricCompatible cov)
    {p : M} {u η : TangentSpace I p} (t₀ : ℝ) :
    ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧ ∀ s ∈ Ioo (t₀ - R) (t₀ + R), ∀ r ∈ Ioo (-δ) δ,
      GExp (cov := cov) hmet p (s • (u + r • η)) ∈
        (chartAt H (GExp (cov := cov) hmet p (t₀ • u))).source := by
  set x₀ : M := GExp (cov := cov) hmet p (t₀ • u) with hx₀def
  have hcont := (contMDiffAt_GExp_family (cov := cov) hmet (p := p) (u := u) (η := η) t₀ 0).continuousAt
  have hsrc : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hmem0 : (fun q : ℝ × ℝ => GExp (cov := cov) hmet p (q.1 • (u + q.2 • η))) (t₀, 0) ∈
      (chartAt H x₀).source := by
    have h1 : (fun q : ℝ × ℝ => GExp (cov := cov) hmet p (q.1 • (u + q.2 • η))) (t₀, 0) = x₀ := by
      rw [hx₀def]; simp
    rw [h1]; exact hsrc
  have hmem := hcont.preimage_mem_nhds ((chartAt H x₀).open_source.mem_nhds hmem0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨ε/2, ε/2, by linarith, by linarith, ?_⟩
  intro s hs r hr
  have hx : (s, r) ∈ Metric.ball (t₀, 0) ε := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    refine ⟨?_, ?_⟩
    · rw [abs_lt]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · rw [abs_lt]; exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hfin := hball hx
  simpa using hfin

/-- **Smoothness of the chart description of the family** in a *fixed* chart. -/
theorem contDiffAt_chartFamily (hmet : IsMetricCompatible cov)
    {p : M} {u η : TangentSpace I p} {x₀ : M} {σ ρ : ℝ}
    (hsrc : GExp (cov := cov) hmet p (σ • (u + ρ • η)) ∈ (chartAt H x₀).source) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ =>
      (extChartAt I x₀) (GExp (cov := cov) hmet p (q.1 • (u + q.2 • η)))) (σ, ρ) := by
  have hfam := contMDiffAt_GExp_family (cov := cov) hmet (p := p) (u := u) (η := η) σ ρ
  have hval : (fun q : ℝ × ℝ => GExp (cov := cov) hmet p (q.1 • (u + q.2 • η))) (σ, ρ)
      ∈ (chartAt H x₀).source := by
    have h1 : (fun q : ℝ × ℝ => GExp (cov := cov) hmet p (q.1 • (u + q.2 • η))) (σ, ρ)
        = GExp (cov := cov) hmet p (σ • (u + ρ • η)) := by simp
    rw [h1]; exact hsrc
  have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I x₀)
      ((fun q : ℝ × ℝ => GExp (cov := cov) hmet p (q.1 • (u + q.2 • η))) (σ, ρ)) :=
    (contMDiffOn_extChartAt (I := I) (x := x₀) (n := ∞)).contMDiffAt
      ((chartAt H x₀).open_source.mem_nhds hval)
  exact ((hchart.comp (σ, ρ) hfam).contDiffAt)

/-- **Smoothness of the chart description of a ray** `σ ↦ (extChartAt I x₀) (GExp q (σ • v))`. -/
theorem contDiffAt_chartRay (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q}
    (hv : v ≠ 0) {x₀ : M} {σ : ℝ}
    (hsrc : GExp (cov := cov) hmet q (σ • v) ∈ (chartAt H x₀).source) :
    ContDiffAt ℝ ∞ (fun x : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet q (x • v))) σ := by
  have hsm : ContMDiffOn 𝓘(ℝ) I ∞ (fun x : ℝ => GExp (cov := cov) hmet q (x • v)) univ :=
    Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hv
  have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I x₀) (GExp (cov := cov) hmet q (σ • v)) :=
    (contMDiffOn_extChartAt (I := I) (x := x₀) (n := ∞)).contMDiffAt
      ((chartAt H x₀).open_source.mem_nhds hsrc)
  exact ((hchart.comp σ (hsm.contMDiffAt (Filter.univ_mem))).contDiffAt)

/-- `curveVelocity` only depends on the germ of the curve (alias). -/
theorem curveVelocity_congr {γ₁ γ₂ : ℝ → M} {t : ℝ} (h : γ₁ =ᶠ[𝓝 t] γ₂) :
    curveVelocity (I := I) γ₁ t = curveVelocity (I := I) γ₂ t :=
  Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) h

/-! ## The main local lemma -/

/-- **The variation field of the family of rays is a Jacobi field.**  For a unit vector `u` and any
perturbation direction `η`, the `r`-variation field of the family `r ↦ GExp p (σ • (u + r • η))` of
rays is a Jacobi field along the ray `σ ↦ GExp p (σ • u)`. -/
theorem isJacobiAt_GExp_variation (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {u η : TangentSpace I p} (hu : u ≠ 0) (hu1 : ‖u‖ = 1) (t₀ : ℝ) :
    IsJacobiAt cov (fun s : ℝ => GExp (cov := cov) hmet p (s • u))
      (fun s : ℝ => curveVelocity (I := I)
        (fun r : ℝ => GExp (cov := cov) hmet p (s • (u + r • η))) 0) t₀ := by
  obtain ⟨R, δ, hR, hδ, hbox⟩ :=
    exists_window_GExp_family (cov := cov) hmet (p := p) (u := u) (η := η) t₀
  have h0δ : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have h0δ' : (0 : ℝ) ∈ Ioo (-δ) δ := h0δ
  set δ₀ : ℝ := min δ (‖u‖ / (2 * (‖η‖ + 1))) with hδ₀def
  have hδ₀pos : 0 < δ₀ := lt_min hδ (by positivity)
  have hδ₀le : δ₀ ≤ δ := min_le_left _ _
  have h0δ₀ : (0 : ℝ) ∈ Ioo (-δ₀) δ₀ := ⟨by linarith, hδ₀pos⟩
  have hvt : ∀ t ∈ Ioo (-δ₀) δ₀, u + t • η ≠ 0 := by
    intro t ht
    have htabs : |t| < δ₀ := abs_lt.mpr ht
    have hη1 : (0 : ℝ) < ‖η‖ + 1 := by positivity
    have h2 : δ₀ * ‖η‖ ≤ ‖u‖ / 2 := by
      have hle : δ₀ ≤ ‖u‖ / (2 * (‖η‖ + 1)) := min_le_right _ _
      have hstep : (‖u‖ / (2 * (‖η‖ + 1))) * ‖η‖ ≤ ‖u‖ / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (show (0:ℝ) < 2 * (‖η‖ + 1) from by positivity)]
        nlinarith [norm_nonneg η, norm_nonneg u]
      exact le_trans (mul_le_mul_of_nonneg_right hle (norm_nonneg η)) hstep
    have h3 : ‖t • η‖ ≤ ‖u‖ / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact le_trans (mul_le_mul_of_nonneg_right htabs.le (norm_nonneg η)) h2
    have h4 : ‖u‖ ≤ ‖u + t • η‖ + ‖t • η‖ := by
      have h := norm_add_le (u + t • η) (-(t • η))
      have h1 : u + t • η + -(t • η) = u := by abel
      rw [h1, norm_neg] at h
      exact h
    have hpos : 0 < ‖u + t • η‖ := by
      have h1 : ‖u‖ / 2 ≤ ‖u + t • η‖ := by linarith
      have h2 : 0 < ‖u‖ / 2 := by rw [hu1]; norm_num
      linarith
    exact norm_pos_iff.mp hpos
  set x₀ : M := GExp (cov := cov) hmet p (t₀ • u) with hx₀
  set Ψ : ℝ × ℝ → E := fun q =>
    (extChartAt I x₀) (GExp (cov := cov) hmet p (q.1 • (u + q.2 • η))) with hΨ
  set ugeo : ℝ → E := fun s => Ψ (s, 0) with hugeo
  set wgeo : ℝ → E := fun s => deriv (fun x : ℝ => Ψ (x, 0)) s with hwgeo
  set y : ℝ → E := fun s => deriv (fun r : ℝ => Ψ (s, r)) 0 with hy
  set Φ : ℝ × ℝ → E × E :=
    fun q => (Ψ (q.1, q.2), deriv (fun x : ℝ => Ψ (x, q.2)) q.1) with hΦ
  have hTGT : ∀ t ∈ Ioo (-δ₀) δ₀, ∀ s ∈ Ioo (t₀ - R) (t₀ + R),
      (Φ (s, t)).1 ∈ (extChartAt I x₀).target := by
    intro t ht s hs
    have htδ : t ∈ Ioo (-δ) δ :=
      ⟨lt_of_le_of_lt (neg_le_neg hδ₀le) ht.1, lt_of_lt_of_le ht.2 hδ₀le⟩
    have hsrc := hbox s hs t htδ
    have hsource : GExp (cov := cov) hmet p (s • (u + t • η)) ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source]; exact hsrc
    have hthis := (extChartAt I x₀).map_source hsource
    rw [hΦ, hΨ]
    exact hthis
  have hODE : ∀ t ∈ Ioo (-δ₀) δ₀, ∀ s ∈ Ioo (t₀ - R) (t₀ + R),
      HasDerivAt (fun s' : ℝ => Φ (s', t)) ((Φ (s, t)).2,
        chartGeodesicVectorField cov x₀ (Φ (s, t))) s := by
    intro t ht s hs
    have htδ : t ∈ Ioo (-δ) δ :=
      ⟨lt_of_le_of_lt (neg_le_neg hδ₀le) ht.1, lt_of_lt_of_le ht.2 hδ₀le⟩
    have hsrc := hbox s hs t htδ
    have hvt' : u + t • η ≠ 0 := hvt t ht
    have hcd : ContDiffAt ℝ ∞ (fun x : ℝ => Ψ (x, t)) s := by
      have h := contDiffAt_chartRay (cov := cov) hmet (q := p) (v := u + t • η) hvt'
        (x₀ := x₀) (σ := s) hsrc
      simpa [hΨ] using h
    have h1 : HasDerivAt (fun s' : ℝ => Ψ (s', t))
        (deriv (fun x : ℝ => Ψ (x, t)) s) s := by
      have h2 : HasDerivAt (fun x : ℝ => x + (0:ℝ)) (1 : ℝ) s := by
        simpa using (hasDerivAt_id s).add_const 0
      have h3 : HasDerivAt (fun x : ℝ => Ψ (x, t))
          (deriv (fun x : ℝ => Ψ (x, t)) s) s :=
        (hcd.differentiableAt (by simp)).hasDerivAt
      simpa using h3
    have hode := hasDerivAt_deriv_chartCurve_of_isGeodesicAt (cov := cov) x₀ isOpen_univ
      (Set.mem_univ s)
      (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hvt')
      hsrc
      (Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hvt' s)
      (Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hvt' s)
    have h2 : HasDerivAt (fun s' : ℝ => deriv (fun x : ℝ => Ψ (x, t)) s')
        (chartGeodesicVectorField cov x₀
          (Ψ (s, t), deriv (fun x : ℝ => Ψ (x, t)) s)) s := by
      simpa [hΨ] using hode
    have hpair := h1.prodMk h2
    rw [hΦ]
    exact hpair
  have hSM : ∀ s ∈ Ioo (t₀ - R) (t₀ + R), ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0) := by
    intro s hs
    have hsrc := hbox s hs 0 h0δ
    have hjoint : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => Ψ (q.1, q.2)) (s, 0) := by
      have h := contDiffAt_chartFamily (cov := cov) hmet (p := p) (u := u) (η := η)
        (x₀ := x₀) (σ := s) (ρ := 0) hsrc
      simpa [hΨ] using h
    have hvel : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ =>
        deriv (fun x : ℝ => Ψ (x, q.2)) q.1) (s, 0) := by
      have hfd : ContDiffAt ℝ ∞ (fderiv ℝ Ψ) (s, 0) :=
        (contDiffAt_chartFamily (cov := cov) hmet (p := p) (u := u) (η := η) (x₀ := x₀)
          (σ := s) (ρ := 0) hsrc).fderiv_right (le_refl (∞ : ℕ∞ω))
      have hmain : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ =>
          (fderiv ℝ Ψ (q.1, q.2)) ((1 : ℝ), (0 : ℝ))) (s, 0) :=
        hfd.clm_apply contDiffAt_const
      refine hmain.congr_of_eventuallyEq ?_
      have hnb : ∀ᶠ q : ℝ × ℝ in 𝓝 (s, 0), q.1 ∈ Ioo (t₀ - R) (t₀ + R) ∧ q.2 ∈ Ioo (-δ) δ := by
        rw [nhds_prod_eq]
        exact Filter.prod_mem_prod (isOpen_Ioo.mem_nhds hs) (isOpen_Ioo.mem_nhds h0δ)
      filter_upwards [hnb] with q hq
      have hsrcq : GExp (cov := cov) hmet p (q.1 • (u + q.2 • η)) ∈ (chartAt H x₀).source :=
        hbox q.1 hq.1 q.2 hq.2
      have hcdq : DifferentiableAt ℝ Ψ (q.1, q.2) :=
        (contDiffAt_chartFamily (cov := cov) hmet (p := p) (u := u) (η := η) (x₀ := x₀)
          (σ := q.1) (ρ := q.2) hsrcq).differentiableAt (by simp)
      exact deriv_slice_fst hcdq
    rw [hΦ]
    exact hjoint.prodMk hvel
  have hODEres := variationField_satisfies_jacobiSys_gen (cov := cov) htor hδ₀pos hR
    (x₀ := x₀) (c := t₀) (Φ := Φ) hTGT hODE hSM
  have hgc : gc Φ = ugeo := by
    funext r; rw [gc_apply, hΦ]
  have hgv : gv Φ = wgeo := by
    funext r; rw [gv_apply, hΦ]
  have hYp : ∀ r : ℝ, Yp Φ r = y r := by
    intro r; rw [Yp_apply, hΦ]
  have hZp : ∀ r ∈ Ioo (t₀ - R) (t₀ + R), Ufun (cov := cov) x₀ Φ r
      = chartCovDeriv cov x₀ ugeo wgeo y r := by
    intro r hr
    have hsrc : GExp (cov := cov) hmet p (r • (u + (0:ℝ) • η)) ∈ (chartAt H x₀).source :=
      hbox r hr 0 h0δ
    have hsrce : GExp (cov := cov) hmet p (r • (u + (0:ℝ) • η)) ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source]; exact hsrc
    have htgt : ugeo r ∈ (extChartAt I x₀).target := by
      have hthis := (extChartAt I x₀).map_source hsrce
      simpa [ugeo, hΨ] using hthis
    have hsrcv : (extChartAt I x₀).symm (ugeo r) ∈ (chartAt H x₀).source := by
      have h3 : (extChartAt I x₀).symm (ugeo r)
          = GExp (cov := cov) hmet p (r • (u + (0:ℝ) • η)) := by
        simpa [ugeo, hΨ] using (extChartAt I x₀).left_inv hsrce
      rw [h3]
      exact hsrc
    have hder : deriv (fun t : ℝ => deriv (fun x : ℝ => Ψ (x, t)) r) 0 = deriv y r := by
      rw [hy]
      exact (hasDerivAt_deriv_partial_swap (F := Ψ) (s₀ := r) (t₀ := 0)
        ((contDiffAt_chartFamily (cov := cov) hmet (p := p) (u := u) (η := η) (x₀ := x₀)
          (σ := r) (ρ := 0) hsrc).of_le (WithTop.coe_le_coe.mpr le_top))).deriv.symm
    have hU : Ufun (cov := cov) x₀ Φ r
        = deriv y r + christoffelEval cov x₀ ((extChartAt I x₀).symm (ugeo r)) (y r)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (ugeo r)) (wgeo r)) := by
      rw [Ufun_apply]
      rw [show Zp Φ r = deriv (fun t : ℝ => deriv (fun x : ℝ => Ψ (x, t)) r) 0 from rfl]
      rw [show Yp Φ r = y r from rfl]
      rw [show gv Φ r = wgeo r from rfl]
      rw [show (extChartAt I x₀).symm ((Φ (r, 0)).1) = (extChartAt I x₀).symm (ugeo r) from rfl]
      rw [chrB, hder]
    rw [hU, chartCovDeriv_apply (I := I) (u := ugeo) (w := wgeo) (y := y) (t := r) htgt]
  have hnb : Ioo (t₀ - R/2) (t₀ + R/2) ∈ 𝓝 t₀ :=
    isOpen_Ioo.mem_nhds ⟨by linarith [hR], by linarith [hR]⟩
  have hmain : ∀ r ∈ Icc (t₀ - R/2) (t₀ + R/2),
      HasDerivAt (fun σ : ℝ => (y σ, chartCovDeriv cov x₀ ugeo wgeo y σ))
        (jacobiSysVec (cov := cov) x₀ ugeo wgeo r
          (y r, chartCovDeriv cov x₀ ugeo wgeo y r)) r := by
    intro r hr
    have hr' : r ∈ Ioo (t₀ - R) (t₀ + R) := ⟨by linarith [hr.1, hR], by linarith [hr.2, hR]⟩
    have hraw := hODEres r hr
    have hval : jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ) r
          (Yp Φ r, Ufun (cov := cov) x₀ Φ r)
        = jacobiSysVec (cov := cov) x₀ ugeo wgeo r
          (y r, chartCovDeriv cov x₀ ugeo wgeo y r) := by
      rw [hgc, hgv, hYp r, hZp r hr']
    rw [hval] at hraw
    have hev : (fun ρ : ℝ => (Yp Φ ρ, Ufun (cov := cov) x₀ Φ ρ))
        =ᶠ[𝓝 r] (fun ρ : ℝ => (y ρ, chartCovDeriv cov x₀ ugeo wgeo y ρ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hr'] with ρ hρ
      rw [hYp ρ, hZp ρ hρ]
    exact (hev.hasDerivAt_iff).mp hraw
  refine ⟨x₀, ugeo, wgeo, y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hnb] with s hs
    have hs' : s ∈ Ioo (t₀ - R) (t₀ + R) := ⟨by linarith [hs.1, hR], by linarith [hs.2, hR]⟩
    have hthis := (extChartAt I x₀).map_source (by
      rw [extChartAt_source]; exact hbox s hs' 0 h0δ)
    simpa [ugeo, hΨ] using hthis
  · filter_upwards [hnb] with s hs
    have hs' : s ∈ Ioo (t₀ - R) (t₀ + R) := ⟨by linarith [hs.1, hR], by linarith [hs.2, hR]⟩
    have hsrc := hbox s hs' 0 h0δ
    have hcd : ContDiffAt ℝ ∞ (fun x : ℝ => Ψ (x, 0)) s := by
      have h := contDiffAt_chartRay (cov := cov) hmet (q := p) (v := u + (0:ℝ) • η)
        (by simpa using hu) (x₀ := x₀) (σ := s) hsrc
      simpa [hΨ] using h
    have hthis := (hcd.differentiableAt (by simp)).hasDerivAt
    simpa [ugeo, wgeo, hΨ] using hthis
  · filter_upwards [hnb] with s hs
    have hs' : s ∈ Ioo (t₀ - R) (t₀ + R) := ⟨by linarith [hs.1, hR], by linarith [hs.2, hR]⟩
    have hsrc := hbox s hs' 0 h0δ
    have hsrce : GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)) ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source]; exact hsrc
    have h1 : GExp (cov := cov) hmet p (s • u)
        = (extChartAt I x₀).symm ((extChartAt I x₀) (GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)))) := by
      rw [(extChartAt I x₀).left_inv hsrce]
      simp
    simpa [ugeo, hΨ] using h1
  · filter_upwards [hnb] with s hs
    have hs' : s ∈ Ioo (t₀ - R) (t₀ + R) := ⟨by linarith [hs.1, hR], by linarith [hs.2, hR]⟩
    have hsrc0 := hbox s hs' 0 h0δ
    have hcd : ContDiffAt ℝ ∞ (fun r : ℝ => Ψ (s, r)) 0 := by
      have h := contDiffAt_chartFamily (cov := cov) hmet (p := p) (u := u) (η := η) (x₀ := x₀)
        (σ := s) (ρ := 0) hsrc0
      have h2 : ContDiffAt ℝ ∞ (fun r : ℝ => (s, r)) (0 : ℝ) := by fun_prop
      have hcomp := h.comp 0 h2
      simpa [Function.comp_def, hΨ] using hcomp
    have htgt : Ψ (s, 0) ∈ (extChartAt I x₀).target := (extChartAt I x₀).map_source (by
      rw [extChartAt_source]; exact hsrc0)
    have hstay : ∀ᶠ r in 𝓝 (0:ℝ), Ψ (s, r) ∈ (extChartAt I x₀).target := by
      filter_upwards [isOpen_Ioo.mem_nhds h0δ] with r hr
      have hthis := (extChartAt I x₀).map_source (show GExp (cov := cov) hmet p (s • (u + r • η))
          ∈ (extChartAt I x₀).source from by rw [extChartAt_source]; exact hbox s hs' r hr)
      simpa [hΨ] using hthis
    have hhu : HasDerivAt (fun r : ℝ => Ψ (s, r)) (y s) 0 := by
      have h := (hcd.differentiableAt (by simp)).hasDerivAt
      simpa [y] using h
    have hcv := curveVelocity_extChartAt_symm (I := I) (x₀ := x₀) (u := fun r : ℝ => Ψ (s, r))
      (t := 0) (v := y s) hhu htgt hstay
    have hev : (fun r : ℝ => (extChartAt I x₀).symm (Ψ (s, r)))
        =ᶠ[𝓝 (0:ℝ)] (fun r : ℝ => GExp (cov := cov) hmet p (s • (u + r • η))) := by
      filter_upwards [isOpen_Ioo.mem_nhds h0δ] with r hr
      have hsrce : GExp (cov := cov) hmet p (s • (u + r • η)) ∈ (extChartAt I x₀).source := by
        rw [extChartAt_source]; exact hbox s hs' r hr
      simpa [hΨ] using (extChartAt I x₀).left_inv hsrce
    have hcv' : curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (s • (u + r • η))) 0
        = frameVector (I := I) x₀ ((extChartAt I x₀).symm (Ψ (s, 0))) (y s) := by
      rw [← curveVelocity_congr (I := I) hev]
      exact hcv
    have hbase : (extChartAt I x₀).symm (Ψ (s, 0)) = GExp (cov := cov) hmet p (s • u) := by
      have hsrce : GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)) ∈ (extChartAt I x₀).source := by
        rw [extChartAt_source]; exact hsrc0
      have h1' : (extChartAt I x₀).symm (Ψ (s, 0))
          = GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)) := by
        simpa [hΨ] using (extChartAt I x₀).left_inv hsrce
      rw [h1']
      simp
    rw [hbase] at hcv'
    exact hcv'.symm
  · filter_upwards [hnb] with s hs
    have hs' : s ∈ Ioo (t₀ - R) (t₀ + R) := ⟨by linarith [hs.1, hR], by linarith [hs.2, hR]⟩
    have hsrc0 := hbox s hs' 0 h0δ
    have htgt : Ψ (s, 0) ∈ (extChartAt I x₀).target := (extChartAt I x₀).map_source (by
      rw [extChartAt_source]; exact hsrc0)
    have hcd : ContDiffAt ℝ ∞ (fun x : ℝ => Ψ (x, 0)) s := by
      have h := contDiffAt_chartRay (cov := cov) hmet (q := p) (v := u + (0:ℝ) • η)
        (by simpa using hu) (x₀ := x₀) (σ := s) hsrc0
      simpa [hΨ] using h
    have hstay : ∀ᶠ x in 𝓝 s, Ψ (x, 0) ∈ (extChartAt I x₀).target := by
      filter_upwards [isOpen_Ioo.mem_nhds hs'] with x hx
      have hthis := (extChartAt I x₀).map_source (show
        GExp (cov := cov) hmet p (x • (u + (0:ℝ) • η)) ∈ (extChartAt I x₀).source from by
          rw [extChartAt_source]; exact hbox x hx 0 h0δ)
      simpa [hΨ] using hthis
    have hhu : HasDerivAt (fun x : ℝ => Ψ (x, 0)) (wgeo s) s := by
      have h := (hcd.differentiableAt (by simp)).hasDerivAt
      simpa [wgeo] using h
    have hcv := curveVelocity_extChartAt_symm (I := I) (x₀ := x₀) (u := fun x : ℝ => Ψ (x, 0))
      (t := s) (v := wgeo s) hhu htgt hstay
    have hev : (fun x : ℝ => (extChartAt I x₀).symm (Ψ (x, 0)))
        =ᶠ[𝓝 s] (fun x : ℝ => GExp (cov := cov) hmet p (x • u)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs'] with x hx
      have hsrce : GExp (cov := cov) hmet p (x • (u + (0:ℝ) • η)) ∈ (extChartAt I x₀).source := by
        rw [extChartAt_source]; exact hbox x hx 0 h0δ
      simpa [hΨ] using (extChartAt I x₀).left_inv hsrce
    have hbase : (extChartAt I x₀).symm (Ψ (s, 0)) = GExp (cov := cov) hmet p (s • u) := by
      have hsrce : GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)) ∈ (extChartAt I x₀).source := by
        rw [extChartAt_source]; exact hsrc0
      have h1' : (extChartAt I x₀).symm (Ψ (s, 0))
          = GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)) := by
        simpa [hΨ] using (extChartAt I x₀).left_inv hsrce
      rw [h1']
      simp
    have hvel : curveVelocity (I := I) (fun x : ℝ => GExp (cov := cov) hmet p (x • u)) s
        = frameVector (I := I) x₀ (GExp (cov := cov) hmet p (s • u)) (wgeo s) := by
      rw [← curveVelocity_congr (I := I) hev, hcv, hbase]
      rfl
    have hspeed : ‖curveVelocity (I := I) (fun x : ℝ => GExp (cov := cov) hmet p (x • u)) s‖ = 1 := by
      rcases eq_or_ne s 0 with h0 | h0
      · subst h0
        have hz : curveVelocity (I := I) (fun x : ℝ => GExp (cov := cov) hmet p (x • u)) 0 = u := by
          simpa using Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hu
        have hn : ‖(show TangentSpace I (GExp (cov := cov) hmet p ((0:ℝ) • u)) from u)‖ = 1 := by
          rw [show GExp (cov := cov) hmet p ((0:ℝ) • u) = p from by
            rw [zero_smul, GlobalExp.GExp_zero]]
          exact hu1
        rw [hz]
        exact hn
      · rw [Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hu h0]
        exact hu1
    rw [hbase, chartGram_apply, ← hvel, real_inner_self_eq_norm_sq, hspeed]
    norm_num
  · filter_upwards [hnb] with s hs
    have hs' : s ∈ Ioo (t₀ - R) (t₀ + R) := ⟨by linarith [hs.1, hR], by linarith [hs.2, hR]⟩
    have hcd : ContDiffAt ℝ 2 Ψ (s, 0) :=
      (contDiffAt_chartFamily (cov := cov) hmet (p := p) (u := u) (η := η) (x₀ := x₀)
        (σ := s) (ρ := 0) (hbox s hs' 0 h0δ)).of_le (WithTop.coe_le_coe.mpr le_top)
    have hthis : HasDerivAt (fun s' : ℝ => deriv (fun t : ℝ => Ψ (s', t)) 0)
        (deriv (fun s' : ℝ => deriv (fun t : ℝ => Ψ (s', t)) 0) s) s := by
      have h := hasDerivAt_deriv_partial_swap (F := Ψ) hcd
      exact h.congr_deriv h.deriv.symm
    exact hthis
  · filter_upwards [hnb] with s hs
    have hr : s ∈ Icc (t₀ - R/2) (t₀ + R/2) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h1 : HasDerivAt (fun σ : ℝ => (y σ, chartCovDeriv cov x₀ ugeo wgeo y σ).2)
        ((jacobiSysVec (cov := cov) x₀ ugeo wgeo s
          (y s, chartCovDeriv cov x₀ ugeo wgeo y s)).2) s := by
      have h0 : HasFDerivAt (fun σ : ℝ => (y σ, chartCovDeriv cov x₀ ugeo wgeo y σ))
          (ContinuousLinearMap.toSpanSingleton ℝ (jacobiSysVec (cov := cov) x₀ ugeo wgeo s
            (y s, chartCovDeriv cov x₀ ugeo wgeo y s))) s :=
        (hasDerivAt_iff_hasFDerivAt).mp (hmain s hr)
      have h := (h0.snd).hasDerivAt
      simpa using h
    exact h1.congr_deriv h1.deriv.symm
  · filter_upwards [hnb] with s hs
    have hr : s ∈ Icc (t₀ - R/2) (t₀ + R/2) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hs' : s ∈ Ioo (t₀ - R) (t₀ + R) := ⟨by linarith [hs.1, hR], by linarith [hs.2, hR]⟩
    have h1 : HasDerivAt (fun σ : ℝ => (y σ, chartCovDeriv cov x₀ ugeo wgeo y σ).2)
        ((jacobiSysVec (cov := cov) x₀ ugeo wgeo s
          (y s, chartCovDeriv cov x₀ ugeo wgeo y s)).2) s := by
      have h0 : HasFDerivAt (fun σ : ℝ => (y σ, chartCovDeriv cov x₀ ugeo wgeo y σ))
          (ContinuousLinearMap.toSpanSingleton ℝ (jacobiSysVec (cov := cov) x₀ ugeo wgeo s
            (y s, chartCovDeriv cov x₀ ugeo wgeo y s))) s :=
        (hasDerivAt_iff_hasFDerivAt).mp (hmain s hr)
      have h := (h0.snd).hasDerivAt
      simpa using h
    have hder : deriv (chartCovDeriv cov x₀ ugeo wgeo y) s
        = (jacobiSysVec (cov := cov) x₀ ugeo wgeo s
            (y s, chartCovDeriv cov x₀ ugeo wgeo y s)).2 := h1.deriv
    have hsrc : GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)) ∈ (chartAt H x₀).source :=
      hbox s hs' 0 h0δ
    have hsrce : GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)) ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source]; exact hsrc
    have htgt : ugeo s ∈ (extChartAt I x₀).target := by
      have hthis2 := (extChartAt I x₀).map_source hsrce
      simpa [ugeo, hΨ] using hthis2
    have hsrcv : (extChartAt I x₀).symm (ugeo s) ∈ (chartAt H x₀).source := by
      have h3 : (extChartAt I x₀).symm (ugeo s)
          = GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)) := by
        simpa [ugeo, hΨ] using (extChartAt I x₀).left_inv hsrce
      rw [h3]
      exact hsrc
    have hbase : (extChartAt I x₀).symm (ugeo s) = GExp (cov := cov) hmet p (s • u) := by
      have h1' : (extChartAt I x₀).symm (ugeo s)
          = GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)) := by
        simpa [ugeo, hΨ] using (extChartAt I x₀).left_inv hsrce
      rw [h1']
      simp
    rw [chartCovDeriv_apply (I := I) (u := ugeo) (w := wgeo)
      (y := chartCovDeriv cov x₀ ugeo wgeo y) (t := s) htgt, hder, jacobiSysVec_apply]
    rw [gammaOp_apply (cov := cov) (x₀ := x₀) (u := ugeo) (w := wgeo) (t := s) hsrcv
        (chartCovDeriv cov x₀ ugeo wgeo y s),
      curvOp_apply (cov := cov) (x₀ := x₀) (u := ugeo) (w := wgeo) (t := s) hsrcv (y s)]
    simp only [neg_one_smul]
    abel

end

end Submission.RayJacobi
