import Submission.Work.RiemLib.CornerCut

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Hopf–Rinow: the existence of minimising geodesics

This file proves the two ingredients of Hopf–Rinow that are needed for the sphere theorem:

* `exists_eq_expMap_of_riemannianEDist_lt`: **the normal ball is covered by the exponential map**.
  There is `ρ > 0` such that every point `q` with `riemannianEDist x₀ q < ρ` is `expMap cov x₀ v`
  for a tangent vector `v` with `‖v‖ = riemannianEDist x₀ q`; in particular the geodesic from `x₀`
  to `q` is minimising.  The proof follows `Minimal.lean`: a path from `x₀` to `q` is lifted to the
  normal coordinates through a local inverse of `expMap`, the radial inequality of `Minimal.lean`
  bounds the radial coordinate by the length of the path, and a closedness induction
  (`IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset`) keeps the lift inside the ball.
* (next) `exists_geodesic_riemannianEDist_eq`: **every two points are joined by a minimising
  geodesic**, by the classical recursion with `Commons.Geometry.Manifold.riemannianEDist_min_on_sphere`
  and the corner-cutting lemma `Submission.CornerCut.corner_cut`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter MeasureTheory
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartBounds
open Submission.GeodesicSpeed
open Submission.Length
open Submission.Minimal
open Submission.Gauss
open Submission.GlobalExp
open Submission.Distance
open Submission.CornerCut

namespace Submission.HopfRinow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

/-- **The normal ball is covered by the exponential map.**  There is `ρ > 0` such that any point
`q` at distance `< ρ` from `x₀` is the exponential of a tangent vector `v` with `‖v‖ = d(x₀,q)`. -/
theorem exists_eq_expMap_of_riemannianEDist_lt [I.Boundaryless] [Nontrivial E]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q : M, Manifold.riemannianEDist I x₀ q < ENNReal.ofReal ρ →
      ∃ v : TangentSpace I x₀, expMap cov x₀ v = q ∧
        Manifold.riemannianEDist I x₀ q = ENNReal.ofReal ‖v‖ := by
  classical
  obtain ⟨ρg, hρg, hgauss⟩ := gauss_lemma_fderiv (cov := cov) hmet htor x₀
  obtain ⟨ρs, hρs, hsm₀⟩ := exists_radius_contMDiffAt_expMap (cov := cov) x₀
  obtain ⟨ρm, hρm, hmin⟩ :=
    Submission.Minimal.riemannianEDist_expMap_eq (I := I) (cov := cov) hmet htor x₀
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := exists_chartGram_bounds (I := I) x₀
    (K := ({x₀} : Set M)) isCompact_singleton ⟨x₀, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact mem_chart_source H x₀)
  have hsqlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hf := isLocalDiffeomorphAt_expMap_zero (cov := cov) x₀
  obtain ⟨ε₁, hε₁, hε₁ball⟩ : ∃ ε > 0, Metric.ball (0 : E) ε ⊆ (Classical.choose hf).source := by
    rcases Metric.isOpen_iff.mp (Classical.choose hf).open_source 0 hf.localInverse_mem_target with
      ⟨ε, hε, hsub⟩
    exact ⟨ε, hε, hsub⟩
  have hcont0 : ContinuousAt (fun v : E => expMap cov x₀ v) 0 :=
    (hsm₀ 0 (by simpa using hρs)).continuousAt
  obtain ⟨r₁, hr₁, hr₁ball⟩ := Metric.mem_nhds_iff.mp (hcont0.preimage_mem_nhds
    (hf.localInverse_open_source.mem_nhds hf.localInverse_mem_source))
  have hr₁sub : ∀ v : E, ‖v‖ < r₁ → expMap cov x₀ v ∈ hf.localInverse.source := fun v hv =>
    hr₁ball (by rw [Metric.mem_ball, dist_zero_right]; exact hv)
  set r : ℝ := min (min ρm (min ρs ρg)) (min r₁ ε₁) / 2 with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    have h : 0 < min (min ρm (min ρs ρg)) (min r₁ ε₁) :=
      lt_min (lt_min hρm (lt_min hρs hρg)) (lt_min hr₁ hε₁)
    exact div_pos h (by norm_num)
  have hr_le_m : r ≤ ρm := by
    rw [hrdef]
    have h1 : min (min ρm (min ρs ρg)) (min r₁ ε₁) ≤ min ρm (min ρs ρg) := min_le_left _ _
    have h2 : min ρm (min ρs ρg) ≤ ρm := min_le_left _ _
    linarith
  have hr_le_s : r ≤ ρs := by
    rw [hrdef]
    have h1 : min (min ρm (min ρs ρg)) (min r₁ ε₁) ≤ min ρm (min ρs ρg) := min_le_left _ _
    have h2 : min ρm (min ρs ρg) ≤ min ρs ρg := min_le_right _ _
    have h3 : min ρs ρg ≤ ρs := min_le_left _ _
    linarith
  have hr_le_g : r ≤ ρg := by
    rw [hrdef]
    have h1 : min (min ρm (min ρs ρg)) (min r₁ ε₁) ≤ min ρm (min ρs ρg) := min_le_left _ _
    have h2 : min ρm (min ρs ρg) ≤ min ρs ρg := min_le_right _ _
    have h3 : min ρs ρg ≤ ρg := min_le_right _ _
    linarith
  have hr_le_1 : r ≤ r₁ := by
    rw [hrdef]
    have h1 : min (min ρm (min ρs ρg)) (min r₁ ε₁) ≤ min r₁ ε₁ := min_le_right _ _
    have h2 : min r₁ ε₁ ≤ r₁ := min_le_left _ _
    linarith
  have hr_le_e : r ≤ ε₁ := by
    rw [hrdef]
    have h1 : min (min ρm (min ρs ρg)) (min r₁ ε₁) ≤ min r₁ ε₁ := min_le_right _ _
    have h2 : min r₁ ε₁ ≤ ε₁ := min_le_right _ _
    linarith
  refine ⟨min (r / 2) (Real.sqrt lam * r / 2),
    lt_min (by positivity) (by positivity), fun q hq => ?_⟩
  have hq1 : Manifold.riemannianEDist I x₀ q < ENNReal.ofReal (r / 2) :=
    lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hq2 : Manifold.riemannianEDist I x₀ q < ENNReal.ofReal (Real.sqrt lam * r / 2) :=
    lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  obtain ⟨γ, hγ0, hγ1, hγC1, hγlen, -, -⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (I := I) hq2 zero_lt_one
  set σ : ℝ → E := fun s => hf.localInverse (γ s) with hσdef
  set σ' : ℝ → E := fun s => (mfderiv I 𝓘(ℝ, E) hf.localInverse (γ s))
      ((mfderiv 𝓘(ℝ) I γ s) (1 : ℝ)) with hσ'def
  set u : Set M := Set.image (fun w : E => expMap cov x₀ w)
      (closure (Metric.ball (0 : E) (r / 2))) with hudef
  set sset : Set ℝ := {t : ℝ | γ t ∈ u} with hsdef
  have hσapp : ∀ s : ℝ, σ s = hf.localInverse (γ s) := fun s => by simp only [hσdef]
  have hclose_ne : (r / 2) ≠ 0 := by linarith [hrpos]
  have hcompact : IsCompact (closure (Metric.ball (0 : E) (r / 2))) := by
    rw [closure_ball (0 : E) hclose_ne]
    exact isCompact_closedBall 0 (r / 2)
  have hcont_exp : ContinuousOn (fun w : E => expMap cov x₀ w)
      (closure (Metric.ball (0 : E) (r / 2))) := by
    intro w hw
    rw [closure_ball (0 : E) hclose_ne] at hw
    have hw' : ‖w‖ ≤ r / 2 := by
      have h := Metric.mem_closedBall.mp hw
      rwa [dist_zero_right] at h
    exact (hsm₀ w (lt_of_le_of_lt hw' (by linarith))).continuousAt.continuousWithinAt
  have hu_closed : IsClosed u := (hcompact.image_of_continuousOn hcont_exp).isClosed
  have hu_mem : ∀ t : ℝ, γ t ∈ u → ∃ w : E, ‖w‖ ≤ r / 2 ∧ γ t = expMap cov x₀ w := by
    intro t ht
    rw [hudef] at ht
    obtain ⟨w, hw, hwt⟩ := ht
    rw [closure_ball (0 : E) hclose_ne] at hw
    refine ⟨w, ?_, hwt.symm⟩
    have h := Metric.mem_closedBall.mp hw
    rwa [dist_zero_right] at h
  have hbase : (0 : ℝ) ∈ sset := by
    rw [hsdef]
    change γ 0 ∈ u
    rw [hγ0, hudef]
    refine ⟨(0 : E), ?_, ?_⟩
    · rw [closure_ball (0 : E) hclose_ne]
      exact Metric.mem_closedBall.mpr (by rw [dist_zero_right, norm_zero]; linarith [hrpos])
    · exact expMap_zero (cov := cov) x₀
  have hstep : ∀ t₁ ∈ Ico (0 : ℝ) 1, Icc (0 : ℝ) t₁ ⊆ sset → sset ∈ 𝓝[>] t₁ := by
    intro t₁ ht₁ hsub
    have ht₁Icc : t₁ ∈ Icc (0 : ℝ) 1 := ⟨ht₁.1, le_of_lt ht₁.2⟩
    have hu_t : ∀ s ∈ Icc (0 : ℝ) t₁, ∃ w : E, ‖w‖ ≤ r / 2 ∧ γ s = expMap cov x₀ w :=
      fun s hs => hu_mem s (hsub hs)
    have hσsrc : ∀ s ∈ Icc (0 : ℝ) t₁, γ s ∈ hf.localInverse.source := by
      intro s hs
      obtain ⟨w, hw, hws⟩ := hu_t s hs
      rw [hws]
      exact hr₁sub w (lt_of_le_of_lt hw (by linarith))
    have hσnorm : ∀ s ∈ Icc (0 : ℝ) t₁, ‖σ s‖ < r := by
      intro s hs
      obtain ⟨w, hw, hws⟩ := hu_t s hs
      have hεmem : w ∈ (Classical.choose hf).source :=
        hε₁ball (by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_le_of_lt hw (by linarith))
      have h1 : σ s = w := by
        rw [hσapp s, hws]
        exact hf.localInverse_left_inv hεmem
      rw [h1]; linarith
    have hσinv : ∀ s ∈ Icc (0 : ℝ) t₁, γ s = expMap cov x₀ (σ s) := by
      intro s hs
      rw [hσapp s]
      exact (hf.localInverse_right_inv (hσsrc s hs)).symm
    have hmapsTo : MapsTo γ (Icc (0 : ℝ) t₁) hf.localInverse.source := hσsrc
    have hσC1 : ContDiffOn ℝ 1 σ (Icc (0 : ℝ) t₁) := by
      have h1 : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0 : ℝ) t₁) := hγC1.contMDiffOn
      have h2 : ContMDiffOn I 𝓘(ℝ, E) 1 hf.localInverse hf.localInverse.source :=
        hf.contmdiffOn_localInverse.of_le (WithTop.coe_le_coe.mpr le_top)
      exact contMDiffOn_iff_contDiffOn.mp (h2.comp h1 hmapsTo)
    have hσd : ∀ s ∈ Icc (0 : ℝ) t₁, HasDerivAt σ (σ' s) s := by
      intro s hs
      have hγmd : MDifferentiableAt 𝓘(ℝ) I γ s := hγC1.mdifferentiableAt one_ne_zero
      have hφmdAt : MDifferentiableAt I 𝓘(ℝ, E) hf.localInverse (γ s) :=
        (hf.contmdiffOn_localInverse.mdifferentiableOn (by norm_num) (γ s)
          (hσsrc s hs)).mdifferentiableAt
          (hf.localInverse_open_source.mem_nhds (hσsrc s hs))
      have hcomp : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) (hf.localInverse ∘ γ) s :=
        hφmdAt.comp s hγmd
      have hdiff : DifferentiableAt ℝ σ s := mdifferentiableAt_iff_differentiableAt.mp hcomp
      have hderiv : deriv σ s = (mfderiv I 𝓘(ℝ, E) hf.localInverse (γ s))
          ((mfderiv 𝓘(ℝ) I γ s) (1 : ℝ)) :=
        (Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (g := hf.localInverse) (γ := γ)
          hφmdAt hγmd).symm
      rw [hσ'def]
      exact hdiff.hasDerivAt.congr_deriv hderiv
    have hvelnorm : ∀ s ∈ Ioo (0 : ℝ) t₁,
        ‖curveVelocity (I := I) γ s‖ₑ
          = ‖(mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s)) (σ' s)‖ₑ := by
      intro s hs
      have hsIcc : s ∈ Icc (0 : ℝ) t₁ := Ioo_subset_Icc_self hs
      have hev : γ =ᶠ[𝓝 s] (fun r => expMap cov x₀ (σ r)) := by
        filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
        exact hσinv r (Ioo_subset_Icc_self hr)
      have hsm' : MDifferentiableAt 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s) :=
        (hsm₀ (σ s) (lt_of_lt_of_le (hσnorm s hsIcc) hr_le_s)).mdifferentiableAt (by norm_num)
      have hvec : curveVelocity (I := I) γ s
          = (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s)) (σ' s) :=
        curveVelocity_eq_exp_deriv (cov := cov) x₀ (hσd s hsIcc) hsm' hev
      rw [enorm_eq_ofReal_norm, enorm_eq_ofReal_norm, hvec, hev.eq_of_nhds]
    have hσ0' : σ 0 = 0 := by
      have h : hf.localInverse (expMap cov x₀ 0) = 0 :=
        hf.localInverse_left_inv hf.localInverse_mem_target
      rw [hσapp 0, hγ0]
      simpa only [expMap_zero] using h
    have hstay_lem := pathELength_ge_radial_of_stays (cov := cov) x₀ (σ := σ) (σ' := σ')
      (R := r) (ρg := ρg) hr_le_g hgauss ht₁Icc hσd hσC1 hσnorm hσ0' hvelnorm
    have hlen_t : Manifold.pathELength I γ 0 t₁ < ENNReal.ofReal (Real.sqrt lam * r / 2) :=
      lt_of_le_of_lt (Manifold.pathELength_mono le_rfl ht₁.2.le) hγlen
    have hRad : Real.sqrt (chartGram (I := I) x₀ x₀ (σ t₁) (σ t₁)) < Real.sqrt lam * r / 2 := by
      have h1 : ENNReal.ofReal (Real.sqrt (chartGram (I := I) x₀ x₀ (σ t₁) (σ t₁)))
          < ENNReal.ofReal (Real.sqrt lam * r / 2) := lt_of_le_of_lt hstay_lem hlen_t
      rwa [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h1
    have hσt_small : ‖σ t₁‖ < r / 2 := by
      have h1 : lam * ‖σ t₁‖ ^ 2 ≤ chartGram (I := I) x₀ x₀ (σ t₁) (σ t₁) :=
        (hbnd x₀ (by simp) (σ t₁)).1
      have h2 : Real.sqrt lam * ‖σ t₁‖
          ≤ Real.sqrt (chartGram (I := I) x₀ x₀ (σ t₁) (σ t₁)) := by
        rw [show Real.sqrt lam * ‖σ t₁‖ = Real.sqrt (lam * ‖σ t₁‖ ^ 2) from by
          rw [Real.sqrt_mul hlam.le (‖σ t₁‖ ^ 2), Real.sqrt_sq (norm_nonneg (σ t₁))]]
        exact Real.sqrt_le_sqrt h1
      have h4 : Real.sqrt lam * ‖σ t₁‖ < Real.sqrt lam * r / 2 := lt_of_le_of_lt h2 hRad
      nlinarith [h4, hsqlam]
    have hW : {t : ℝ | γ t ∈ hf.localInverse.source ∧ ‖hf.localInverse (γ t)‖ < r / 2} ∈ 𝓝 t₁ := by
      have ht₁self : t₁ ∈ Icc (0 : ℝ) t₁ := ⟨ht₁.1, le_rfl⟩
      have hγt_src : γ t₁ ∈ hf.localInverse.source := hσsrc t₁ ht₁self
      have hcont_φ : ContinuousAt hf.localInverse (γ t₁) :=
        hf.contmdiffOn_localInverse.continuousOn.continuousAt
          (hf.localInverse_open_source.mem_nhds hγt_src)
      have hcont : ContinuousAt (fun t => hf.localInverse (γ t)) t₁ :=
        hcont_φ.comp hγC1.continuous.continuousAt
      have hmem : {t : ℝ | hf.localInverse (γ t) ∈ Metric.ball (0 : E) (r / 2)} ∈ 𝓝 t₁ :=
        hcont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by
          rw [Metric.mem_ball, dist_zero_right, ← hσapp t₁]; exact hσt_small))
      have hmem2 : {t : ℝ | γ t ∈ hf.localInverse.source} ∈ 𝓝 t₁ :=
        hγC1.continuous.continuousAt.preimage_mem_nhds
          (hf.localInverse_open_source.mem_nhds hγt_src)
      filter_upwards [hmem, hmem2] with t ht ht2
      exact ⟨ht2, by rwa [Metric.mem_ball, dist_zero_right] at ht⟩
    show sset ∈ 𝓝 t₁ ⊓ Filter.principal (Ioi t₁)
    rw [Filter.mem_inf_principal]
    refine Filter.mem_of_superset hW ?_
    rintro t ⟨htφ, htφ4⟩ htIoi
    rw [hsdef, hudef]
    refine ⟨hf.localInverse (γ t), ?_, ?_⟩
    · rw [closure_ball (0 : E) hclose_ne]
      exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; linarith)
    · exact hf.localInverse_right_inv htφ
  have hIcc : Icc (0 : ℝ) 1 ⊆ sset :=
    ((hu_closed.preimage hγC1.continuous).inter isClosed_Icc)
      |>.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hbase hstep
  have hqu : q ∈ u := by
    rw [← hγ1]
    exact hIcc ⟨zero_le_one, le_rfl⟩
  have hγ1u : γ 1 ∈ u := by rw [hγ1]; exact hqu
  obtain ⟨w, hw, hwq⟩ := hu_mem 1 hγ1u
  have hwsmall : ‖w‖ < ρm := lt_of_le_of_lt hw (by linarith [hr_le_m, hrpos])
  have hsqrt : Real.sqrt (chartGram (I := I) x₀ x₀ w w)
      = ‖(show TangentSpace I x₀ from w)‖ := by
    haveI : FiniteDimensional ℝ (TangentSpace I x₀) := inferInstanceAs (FiniteDimensional ℝ E)
    rw [chartGram_self_apply (I := I) x₀ w w, real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _)]
  refine ⟨(show TangentSpace I x₀ from w), ?_, ?_⟩
  · rw [← hwq, hγ1]
  · rw [← hγ1, hwq, hmin w hwsmall, hsqrt]


/-! ## Continuity of the Riemannian distance, finiteness, and the distance spheres -/

/-- **The Riemannian distance to a fixed point is continuous.** -/
theorem continuous_riemannianEDist_left [RegularSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] (p : M) :
    Continuous (fun y : M => Manifold.riemannianEDist I p y) := by
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have h1 : Continuous (fun y : M => edist p y) := by fun_prop
  refine h1.congr (fun y => ?_)
  exact (Submission.EDist.edist_eq_riemannianEDist (I := I) p y).symm

/-- **The Riemannian distance from a fixed point is continuous.** -/
theorem continuous_riemannianEDist_right [RegularSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] (q : M) :
    Continuous (fun y : M => Manifold.riemannianEDist I y q) := by
  have h1 : Continuous (fun y : M => Manifold.riemannianEDist I q y) :=
    continuous_riemannianEDist_left (I := I) q
  refine h1.congr (fun y => ?_)
  exact Manifold.riemannianEDist_comm (I := I)

/-- **The Riemannian distance is everywhere finite** on a connected manifold. -/
theorem riemannianEDist_lt_top [I.Boundaryless] [Nontrivial E] [ConnectedSpace M]
    [RegularSpace M] {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (p q : M) : Manifold.riemannianEDist I p q < ⊤ := by
  haveI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hnear : ∀ x : M, ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : M,
      Manifold.riemannianEDist I x y < ENNReal.ofReal ρ →
      Manifold.riemannianEDist I x y < ⊤ := fun x => by
    obtain ⟨ρ, hρ, _⟩ := exists_eq_expMap_of_riemannianEDist_lt (I := I) (cov := cov) hmet htor x
    exact ⟨ρ, hρ, fun y hy => lt_of_lt_of_le hy ENNReal.ofReal_lt_top.le⟩
  have hopen : IsOpen {x : M | Manifold.riemannianEDist I p x < ⊤} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨ρ, hρ, hρ'⟩ := hnear x
    refine Filter.mem_of_superset
      (Submission.EDist.eventually_riemannianEDist_lt (I := I) x (ENNReal.ofReal_pos.mpr hρ))
      (fun y hy => ?_)
    exact lt_of_le_of_lt (Manifold.riemannianEDist_triangle (I := I))
      (ENNReal.add_lt_top.mpr ⟨hx, hρ' y hy⟩)
  have hclosed : IsClosed {x : M | Manifold.riemannianEDist I p x < ⊤} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx
    have hxT : Manifold.riemannianEDist I p x = ⊤ := eq_top_iff.mpr (not_lt.mp hx)
    obtain ⟨ρ, hρ, hρ'⟩ := hnear x
    refine Filter.mem_of_superset
      (Submission.EDist.eventually_riemannianEDist_lt (I := I) x (ENNReal.ofReal_pos.mpr hρ))
      (fun y hy hyfin => ?_)
    have htri := Manifold.riemannianEDist_triangle (I := I) (x := p) (y := y) (z := x)
    rw [hxT] at htri
    exact absurd htri (not_le.mpr (ENNReal.add_lt_top.mpr ⟨hyfin,
      (Manifold.riemannianEDist_comm (I := I) (x := y) (y := x)).trans_lt (hρ' y hy)⟩))
  have huniv : {x : M | Manifold.riemannianEDist I p x < ⊤} = Set.univ := by
    rcases isClopen_iff.mp ⟨hclosed, hopen⟩ with h | h
    · exfalso
      have hp : p ∈ ({x : M | Manifold.riemannianEDist I p x < ⊤} : Set M) := by
        show Manifold.riemannianEDist I p p < ⊤
        rw [Manifold.riemannianEDist_self]
        exact ENNReal.zero_lt_top
      rw [h] at hp
      exact hp
    · exact h
  exact (show q ∈ ({x : M | Manifold.riemannianEDist I p x < ⊤} : Set M) from
    huniv ▸ Set.mem_univ q)

/-- **There is a point at Riemannian distance exactly `r` from `p`**, for `0 < r < d(p,q)`, on a
path connected manifold. -/
theorem exists_riemannianEDist_eq_ofReal [PathConnectedSpace M] [RegularSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] (p q : M)
    {r : ℝ} (hr : 0 < r) (hrL : ENNReal.ofReal r < Manifold.riemannianEDist I p q) :
    ∃ z : M, Manifold.riemannianEDist I p z = ENNReal.ofReal r := by
  set γ : Path p q := (PathConnectedSpace.joined p q).somePath with hγdef
  have hγ0 : γ (0 : Set.Icc (0 : ℝ) 1) = p := Path.source γ
  have hγ1 : γ (1 : Set.Icc (0 : ℝ) 1) = q := Path.target γ
  set F : ℝ → M := fun t => γ (Set.projIcc (0 : ℝ) 1 zero_le_one t) with hFdef
  have hFcontM : Continuous F := by
    rw [hFdef]
    exact γ.continuous.comp continuous_projIcc
  have hFcont : ContinuousOn (fun t : ℝ => Manifold.riemannianEDist I p (F t)) (Icc (0 : ℝ) 1) :=
    ((continuous_riemannianEDist_left (I := I) p).comp hFcontM).continuousOn
  have h0 : F 0 = p := by
    rw [hFdef]
    show γ (Set.projIcc (0 : ℝ) 1 zero_le_one 0) = p
    rw [Set.projIcc_left]
    simpa using hγ0
  have h1 : F 1 = q := by
    rw [hFdef]
    show γ (Set.projIcc (0 : ℝ) 1 zero_le_one 1) = q
    rw [Set.projIcc_right]
    simpa using hγ1
  have hmem : ENNReal.ofReal r ∈ Icc (Manifold.riemannianEDist I p (F 0))
      (Manifold.riemannianEDist I p (F 1)) := by
    rw [h0, h1, Manifold.riemannianEDist_self]
    exact ⟨le_of_lt (ENNReal.ofReal_pos.mpr hr), le_of_lt hrL⟩
  obtain ⟨t, ht, hFt⟩ := (intermediate_value_Icc zero_le_one hFcont) hmem
  exact ⟨F t, hFt⟩

end

end Submission.HopfRinow
