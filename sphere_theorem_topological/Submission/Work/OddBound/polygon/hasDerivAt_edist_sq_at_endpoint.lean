import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.ConjEnergy
import Submission.Work.OddBound.longHomotopy.gauss_pairing_fibre
import Submission.Work.OddBound.longHomotopy.gauss_pairing_rescale
import Submission.Work.OddBound.polygon.minimiser_unique_of_mem_segmentDomain
import Submission.HopfRinow2
import Submission.Work.OddBound.polygon.minimisers_cluster_near_segmentDomain
import Submission.Work.OddBound.polygon.curveVelocity_GExp_ray_one_eq_neg

namespace Work.OddBound.polygon

set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Manifold Topology
open Bundle
open Filter
open Submission.GlobalExp

/-- The chart components of a curve through `x₀` have derivative the curve velocity. -/
private lemma hasDerivAt_extChartAt_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {x₀ : M} {σ : ℝ → M} (hσ0 : σ 0 = x₀) (hσ : MDifferentiableAt 𝓘(ℝ) I σ 0) :
    HasDerivAt (fun s : ℝ => (extChartAt I x₀) (σ s))
      (Submission.Geodesic.curveVelocity (I := I) σ 0) 0 := by
  have he : MDifferentiableAt I 𝓘(ℝ, E) (fun z : M => (extChartAt I x₀) z) (σ 0) := by
    rw [hσ0]
    exact mdifferentiableAt_extChartAt (I := I) (x := x₀) (y := x₀) (mem_chart_source H x₀)
  show HasDerivAt ((fun z : M => (extChartAt I x₀) z) ∘ σ)
    (Submission.Geodesic.curveVelocity (I := I) σ 0) 0
  have hcomp : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E)
      ((fun z : M => (extChartAt I x₀) z) ∘ σ) 0 :=
    MDifferentiableAt.comp (I := 𝓘(ℝ)) (I' := I) (I'' := 𝓘(ℝ, E)) (x := (0:ℝ))
      (f := σ) (g := fun z : M => (extChartAt I x₀) z) he hσ
  have hdiff : DifferentiableAt ℝ ((fun z : M => (extChartAt I x₀) z) ∘ σ) 0 :=
    (mdifferentiableAt_iff_differentiableAt).mp hcomp
  have hval : (fderiv ℝ ((fun z : M => (extChartAt I x₀) z) ∘ σ) 0) 1
      = Submission.Geodesic.curveVelocity (I := I) σ 0 := by
    have h1 : mfderiv 𝓘(ℝ) 𝓘(ℝ, E) ((fun z : M => (extChartAt I x₀) z) ∘ σ) 0
        = mfderiv 𝓘(ℝ) I σ 0 := by
      have hchain := mfderiv_comp (I := 𝓘(ℝ)) (I' := I) (I'' := 𝓘(ℝ, E)) (x := (0:ℝ))
        (f := σ) (g := fun z : M => (extChartAt I x₀) z) he hσ
      rw [hσ0] at hchain
      rw [hchain, mfderiv_extChartAt_self]
      exact ContinuousLinearMap.id_comp _
    rw [← mfderiv_eq_fderiv, h1]
    rfl
  rw [← hval]
  exact hdiff.hasFDerivAt.hasDerivAt

/-- **First variation of the squared distance at a non-cut point.**

Let `U` be a vector of the tangential segment domain at `q` (so the ray of `U` is *strictly*
minimising at `‖U‖`, i.e. `p = GExp q U` is not a cut point of `q`), and let `w` at `p` be a
minimising vector from `p` to `q` of the same length.  Then for every smooth curve `v` with
`v 0 = p`,

  `d/dt (d(q, v t)²) = -2 ⟪w, v'(0)⟫`  at `t = 0`.

This is the first variation formula of the distance function at a non-cut point. -/
theorem hasDerivAt_edist_sq_at_endpoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {U : TangentSpace I q} (hU : U ≠ 0)
    (hseg : U ∈ Submission.SegmentDomain.segmentDomain hmet q)
    {p : M} (hUp : Submission.GlobalExp.GExp (cov := cov) hmet q U = p)
    {w : TangentSpace I p} (hw : Submission.GlobalExp.GExp (cov := cov) hmet p w = q)
    (hwn : ‖w‖ = ‖U‖)
    {v : ℝ → M} (hv : ContMDiff 𝓘(ℝ) I ∞ v) (hv0 : v 0 = p) :
    HasDerivAt (fun t : ℝ => ((Manifold.riemannianEDist I q (v t)).toReal) ^ 2)
      (-2 * inner ℝ w (Submission.Geodesic.curveVelocity (I := I) v 0)) 0 := by
  classical
  -- replace `p` by the explicit term `GExp q U` (definitional equality bookkeeping)
  subst hUp
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  -- ## 0. basic facts
  have hL : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hpt : Manifold.riemannianEDist I q (GExp (cov := cov) hmet q U) = ENNReal.ofReal ‖U‖ :=
    Submission.SegmentDomain.edist_GExp_eq_norm_of_mem_segmentDomain hmet htor hseg
  -- ## 1. the inverse-function-theorem ball around `U`
  obtain ⟨r₀, hr₀, hball⟩ :=
    Submission.XuMain.exists_pos_ball_lift_GExp_forall_le (cov := cov) hmet q (v := U)
      (Submission.ConjEnergy.isInvertible_mfderiv_of_mem_segmentDomain (cov := cov) hmet htor hseg hU)
  set r : ℝ := r₀ / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hrle : r ≤ r₀ := by rw [hrdef]; linarith
  obtain ⟨δr, hδr, hinj, _hlift⟩ := hball r hr hrle
  -- the model norm and the fibre norm at `q` are comparable
  obtain ⟨lam, hlam, Lam, hΛam, hbnd⟩ := Submission.XuMain.exists_pos_model_fibre_norm (I := I) q
  set sl : ℝ := Real.sqrt lam with hsldef
  have hsl : 0 < sl := by rw [hsldef]; exact Real.sqrt_pos.mpr hlam
  -- the fibre-norm radius corresponding to the model-norm radius `r`
  set r₂ : ℝ := sl * r with hr₂def
  have hr₂ : 0 < r₂ := by rw [hr₂def]; positivity
  -- ## 2. the local inverse `ψ` of `GExp q` at `U`, in the chart at `GExp q U`
  have hAinv : (mfderiv 𝓘(ℝ, E) I (fun w : E => GExp (cov := cov) hmet q w)
      (show E from U)).IsInvertible :=
    Submission.ConjEnergy.isInvertible_mfderiv_of_mem_segmentDomain (cov := cov) hmet htor hseg hU
  set A : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I (fun w : E => GExp (cov := cov) hmet q w)
      (show E from U) with hAdef
  have hAinv' : A.IsInvertible := by
    rw [hAdef]
    exact hAinv
  obtain ⟨Ae, hAe⟩ := hAinv'
  have hGExp_diff : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun u : E => GExp (cov := cov) hmet q (show TangentSpace I q from u))
      (show E from U) :=
    Submission.GExpLocalInj.contMDiffAt_GExp_one (cov := cov) hmet q (show E from U)
  set Ψ : E → E := fun u => (extChartAt I (GExp (cov := cov) hmet q U))
      (GExp (cov := cov) hmet q (show TangentSpace I q from u)) with hΨdef
  have hΨdiff : ContDiffAt ℝ 1 Ψ (show E from U) := by
    have h2 := (contMDiffAt_iff_target.mp hGExp_diff).2
    have h3 : (⇑(extChartAt I (GExp (cov := cov) hmet q U))) ∘
        (fun u : E => GExp (cov := cov) hmet q (show TangentSpace I q from u)) = Ψ := rfl
    rw [h3] at h2
    exact h2.contDiffAt
  have hΨderiv : fderiv ℝ Ψ (show E from U) = (Ae : E →L[ℝ] E) := by
    have key : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ (show E from U) = (Ae : E →L[ℝ] E) := by
      have hchain := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E)) (x := (show E from U))
        (f := fun u : E => GExp (cov := cov) hmet q (show TangentSpace I q from u))
        (g := fun z : M => (extChartAt I (GExp (cov := cov) hmet q U)) z)
        (mdifferentiableAt_extChartAt (I := I) (x := GExp (cov := cov) hmet q U)
          (y := GExp (cov := cov) hmet q U) (mem_chart_source H _))
        (hGExp_diff.mdifferentiableAt one_ne_zero)
      have h4 : (fun z : M => (extChartAt I (GExp (cov := cov) hmet q U)) z) ∘
          (fun u : E => GExp (cov := cov) hmet q (show TangentSpace I q from u)) = Ψ := rfl
      rw [h4] at hchain
      rw [hchain, mfderiv_extChartAt_self, ContinuousLinearMap.id_comp]
      rw [hAe]
    rw [← mfderiv_eq_fderiv]
    exact key
  have hstrict : HasStrictFDerivAt Ψ (Ae : E →L[ℝ] E) (show E from U) := by
    have h := hΨdiff.hasStrictFDerivAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
    rwa [hΨderiv] at h
  set ψ : E → E := hstrict.localInverse Ψ Ae (show E from U) with hψdef
  have hψ_image : ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (GExp (cov := cov) hmet q U))
      = show E from U := hstrict.localInverse_apply_image
  have hψ_right : ∀ᶠ z in 𝓝 ((extChartAt I (GExp (cov := cov) hmet q U))
        (GExp (cov := cov) hmet q U)),
      (extChartAt I (GExp (cov := cov) hmet q U))
        (GExp (cov := cov) hmet q (show TangentSpace I q from ψ z)) = z :=
    hstrict.eventually_right_inverse
  have hψ_deriv : HasFDerivAt ψ (Ae.symm : E →L[ℝ] E)
      ((extChartAt I (GExp (cov := cov) hmet q U)) (GExp (cov := cov) hmet q U)) :=
    hstrict.to_localInverse.hasFDerivAt
  have hψ_cont : ContinuousAt ψ
      ((extChartAt I (GExp (cov := cov) hmet q U)) (GExp (cov := cov) hmet q U)) :=
    hψ_deriv.continuousAt
  -- ## 3. the clustering input (minimising vectors near `GExp q U` are near `U`)
  obtain ⟨ε, hε, hcluster⟩ :=
    Work.OddBound.polygon.minimisers_cluster_near_segmentDomain (cov := cov) hmet htor hU hseg
      (p := GExp (cov := cov) hmet q U) rfl hr₂
  -- ## 4. the ray of `U` arrives at `GExp q U` with velocity `-w`
  have hray : Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet q (s • U)) 1 = -w :=
    Work.OddBound.polygon.curveVelocity_GExp_ray_one_eq_neg (cov := cov) hmet htor hU hseg
      (p := GExp (cov := cov) hmet q U) rfl hw hwn
  -- ## 5. continuity data around `t = 0`
  have hv_cont : ContinuousAt v 0 := (hv 0).continuousAt
  have hv_md : MDifferentiableAt 𝓘(ℝ) I v 0 :=
    (hv 0).mdifferentiableAt (by norm_num : (∞ : ℕ∞ω) ≠ 0)
  have hchart_cont : ContinuousAt
      (fun t : ℝ => (extChartAt I (GExp (cov := cov) hmet q U)) (v t)) 0 :=
    ContinuousAt.comp (f := v) (g := fun z : M => (extChartAt I (GExp (cov := cov) hmet q U)) z)
      (by
        rw [hv0]
        exact continuousAt_extChartAt (I := I) (GExp (cov := cov) hmet q U)) hv_cont
  have htend_chart : Tendsto (fun t : ℝ => (extChartAt I (GExp (cov := cov) hmet q U)) (v t))
      (𝓝 0) (𝓝 ((extChartAt I (GExp (cov := cov) hmet q U)) (GExp (cov := cov) hmet q U))) := by
    have h := hchart_cont.tendsto
    simpa [hv0] using h
  have hψ_cont' : ContinuousAt ψ
      ((extChartAt I (GExp (cov := cov) hmet q U)) (v 0)) := by
    rw [hv0]
    exact hψ_cont
  have hψt_cont : ContinuousAt
      (fun t : ℝ => ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t))) 0 :=
    ContinuousAt.comp (f := fun t : ℝ => (extChartAt I (GExp (cov := cov) hmet q U)) (v t))
      (g := ψ) hψ_cont' hchart_cont
  have hψt_near : ∀ᶠ t in 𝓝 (0:ℝ),
      ‖ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t)) - (show E from U)‖ < r := by
    have hlim : Tendsto (fun t : ℝ => ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t)))
        (𝓝 0) (𝓝 (ψ ((extChartAt I (GExp (cov := cov) hmet q U))
          (GExp (cov := cov) hmet q U)))) := by
      have h := hψt_cont.tendsto
      simpa [hv0] using h
    have hlim' : Tendsto (fun t : ℝ => ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t)))
        (𝓝 0) (𝓝 (show E from U)) := by
      rw [hψ_image] at hlim
      exact hlim
    filter_upwards [hlim'.eventually (Metric.ball_mem_nhds (show E from U) hr)] with t ht
    simpa only [Metric.mem_ball, dist_eq_norm] using ht
  have hψ_right_ev : ∀ᶠ t in 𝓝 (0:ℝ),
      (extChartAt I (GExp (cov := cov) hmet q U))
        (GExp (cov := cov) hmet q
          (show TangentSpace I q from ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t))))
        = (extChartAt I (GExp (cov := cov) hmet q U)) (v t) :=
    htend_chart.eventually hψ_right
  have hvt_src : ∀ᶠ t in 𝓝 (0:ℝ), v t ∈ (extChartAt I (GExp (cov := cov) hmet q U)).source := by
    have h1 : (extChartAt I (GExp (cov := cov) hmet q U)).source ∈ 𝓝 (v 0) := by
      rw [hv0]
      exact extChartAt_source_mem_nhds (I := I) (GExp (cov := cov) hmet q U)
    exact hv_cont.preimage_mem_nhds h1
  have hGt_cont : ContinuousAt (fun t : ℝ =>
      GExp (cov := cov) hmet q
        (show TangentSpace I q from ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t)))) 0 :=
    ContinuousAt.comp (f := fun t : ℝ =>
        ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t)))
      (g := fun u : E => GExp (cov := cov) hmet q (show TangentSpace I q from u))
      (by
        rw [hv0, hψ_image]
        exact hGExp_diff.continuousAt) hψt_cont
  have hGt_src : ∀ᶠ t in 𝓝 (0:ℝ),
      GExp (cov := cov) hmet q
        (show TangentSpace I q from ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t)))
        ∈ (extChartAt I (GExp (cov := cov) hmet q U)).source := by
    have h1 : (extChartAt I (GExp (cov := cov) hmet q U)).source ∈ 𝓝
        (GExp (cov := cov) hmet q
          (show TangentSpace I q from ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v 0)))) := by
      rw [hv0, hψ_image]
      exact extChartAt_source_mem_nhds (I := I) (GExp (cov := cov) hmet q U)
    exact hGt_cont.preimage_mem_nhds h1
  have hhit : ∀ᶠ t in 𝓝 (0:ℝ),
      GExp (cov := cov) hmet q
        (show TangentSpace I q from ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t))) = v t := by
    filter_upwards [hψ_right_ev, hvt_src, hGt_src] with t h1 h2 h3
    exact (extChartAt I (GExp (cov := cov) hmet q U)).injOn h3 h2 h1
  have hsmall_ev : ∀ᶠ t in 𝓝 (0:ℝ),
      Manifold.riemannianEDist I (GExp (cov := cov) hmet q U) (v t) < ENNReal.ofReal ε := by
    have hlim : Tendsto (fun t : ℝ => Manifold.riemannianEDist I (GExp (cov := cov) hmet q U) (v t))
        (𝓝 0) (𝓝 (Manifold.riemannianEDist I (GExp (cov := cov) hmet q U) (v 0))) :=
      (ContinuousAt.comp (f := v)
        (g := fun y : M => Manifold.riemannianEDist I (GExp (cov := cov) hmet q U) y)
        (Submission.HopfRinow.continuous_riemannianEDist_left (I := I)
          (GExp (cov := cov) hmet q U)).continuousAt hv_cont).tendsto
    have hlim' : Tendsto (fun t : ℝ => Manifold.riemannianEDist I (GExp (cov := cov) hmet q U) (v t))
        (𝓝 0) (𝓝 (Manifold.riemannianEDist I (GExp (cov := cov) hmet q U)
          (GExp (cov := cov) hmet q U))) := by
      simpa [hv0] using hlim
    have hmem : Set.Iio (ENNReal.ofReal ε) ∈ 𝓝
        (Manifold.riemannianEDist I (GExp (cov := cov) hmet q U)
          (GExp (cov := cov) hmet q U)) := by
      rw [Manifold.riemannianEDist_self]
      exact isOpen_Iio.mem_nhds (ENNReal.ofReal_pos.mpr hε)
    filter_upwards [hlim'.eventually hmem] with t ht
    exact ht
  -- ## 6. the distance near `GExp q U` is the norm of the local lift
  have hdist_eq : ∀ᶠ t in 𝓝 (0:ℝ),
      (Manifold.riemannianEDist I q (v t)).toReal
        = ‖(show TangentSpace I q from
            ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t)))‖ := by
    filter_upwards [hsmall_ev, hhit, hψt_near] with t hsmall hht hψnear
    obtain ⟨V, hGV, hVd⟩ :=
      Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor q (v t)
    have hVnear : ‖V - U‖ < r₂ := hcluster (v t) hsmall V hGV hVd
    have hVmem : (show E from V) ∈ Metric.closedBall (show E from U) r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : ‖(show E from V) - (show E from U)‖ = ‖(show E from (V - U))‖ := rfl
      rw [h1]
      exact (calc ‖(show E from (V - U))‖ ≤ ‖V - U‖ / sl := (hbnd (V - U)).1
        _ < r₂ / sl := by
            rw [div_lt_div_iff_of_pos_right hsl]
            exact hVnear
        _ = r := by
            rw [hr₂def, mul_div_cancel_left₀ _ (ne_of_gt hsl)]).le
    have hψmem : (show E from ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t)))
        ∈ Metric.closedBall (show E from U) r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hψnear.le
    have himg : Submission.XuLift.gexpMap (cov := cov) hmet q (show E from V)
        = Submission.XuLift.gexpMap (cov := cov) hmet q
          (show E from ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t))) := by
      rw [Submission.XuLift.gexpMap_apply, Submission.XuLift.gexpMap_apply, hGV, hht]
    have heq := hinj hVmem hψmem himg
    rw [hVd, ENNReal.toReal_ofReal (norm_nonneg V)]
    have hnorm : ‖V‖ = ‖(show TangentSpace I q from
        ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t)))‖ := by
      rw [← heq]
    rw [hnorm]
  -- ## 7. derivatives
  have hchart_deriv : HasDerivAt
      (fun t : ℝ => (extChartAt I (GExp (cov := cov) hmet q U)) (v t))
      (show E from Submission.Geodesic.curveVelocity (I := I) v 0) 0 :=
    hasDerivAt_extChartAt_comp (I := I) (x₀ := GExp (cov := cov) hmet q U) hv0 hv_md
  have hψc : HasDerivAt (fun t : ℝ => ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t)))
      (Ae.symm (show E from Submission.Geodesic.curveVelocity (I := I) v 0)) 0 := by
    have h2 : HasFDerivAt ψ (Ae.symm : E →L[ℝ] E)
        ((extChartAt I (GExp (cov := cov) hmet q U)) (v 0)) := by
      rw [hv0]
      exact hψ_deriv
    exact h2.comp_hasDerivAt 0 hchart_deriv
  have hψc' : HasDerivAt
      (fun t : ℝ => (show TangentSpace I q from
        ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t))))
      (show TangentSpace I q from
        Ae.symm (show E from Submission.Geodesic.curveVelocity (I := I) v 0)) 0 :=
    hψc
  have hnorm2 := hψc'.norm_sq
  have hval0 : (show TangentSpace I q from
      ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v 0))) = U := by
    rw [hv0, hψ_image]
  rw [hval0] at hnorm2
  -- ## 8. the Gauss pairing
  set X : E := show E from Submission.Geodesic.curveVelocity (I := I) v 0 with hXdef
  set Z : TangentSpace I q := show TangentSpace I q from Ae.symm X with hZdef
  have hvar := Work.OddBound.longHomotopy.curveVelocity_GExp_smul_variation (cov := cov) hmet 1 U Z
  rw [show ((1 : ℝ) • (U : TangentSpace 𝓘(ℝ, E) (show E from U))) = (show E from U) from
    one_smul ℝ _] at hvar
  rw [show ((1 : ℝ) • (Z : TangentSpace 𝓘(ℝ, E) (show E from U))) = (show E from Z) from
    one_smul ℝ _] at hvar
  rw [← hAdef] at hvar
  have hAZ : A (show E from Z) = (show E from X) := by
    rw [hZdef] at *
    rw [← hAe]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  have hfirst : Submission.Geodesic.curveVelocity (I := I)
      (fun r : ℝ => GExp (cov := cov) hmet q ((1 : ℝ) • (U + r • Z))) 0
      = (show TangentSpace I (GExp (cov := cov) hmet q U) from X) :=
    hvar.trans hAZ
  have hpair : inner ℝ U Z = -inner ℝ w (show TangentSpace I (GExp (cov := cov) hmet q U) from X) := by
    have hpt : GExp (cov := cov) hmet q ((1 : ℝ) • (U + (0 : ℝ) • Z))
        = GExp (cov := cov) hmet q U := by
      rw [zero_smul, add_zero, one_smul]
    have hgauss := hpt ▸ (Work.OddBound.longHomotopy.gauss_pairing_fibre (cov := cov) hmet htor
      (p := q) (v := U) (η := Z) 1)
    have hsecond : Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => GExp (cov := cov) hmet q (s • U)) 1 = -w := hray
    rw [hsecond] at hgauss
    rw [show Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => GExp (cov := cov) hmet q ((1 : ℝ) • (U + r • Z))) 0
        = (show TangentSpace I (GExp (cov := cov) hmet q U) from X) from hfirst] at hgauss
    rw [one_mul] at hgauss
    rw [inner_neg_right] at hgauss
    rw [real_inner_comm] at hgauss
    conv at hgauss => rhs; rw [real_inner_comm]
    exact hgauss.symm
  have hval : 2 * inner ℝ U (show TangentSpace I q from
        Ae.symm (show E from Submission.Geodesic.curveVelocity (I := I) v 0))
      = -2 * inner ℝ w (Submission.Geodesic.curveVelocity (I := I) v 0) := by
    have hZU : (show TangentSpace I q from
        Ae.symm (show E from Submission.Geodesic.curveVelocity (I := I) v 0)) = Z := rfl
    rw [hZU]
    have hX : (show TangentSpace I (GExp (cov := cov) hmet q U) from X)
        = Submission.Geodesic.curveVelocity (I := I) v 0 := rfl
    rw [hpair, hX]
    ring
  -- ## 9. assemble
  have hfun : (fun t : ℝ => ((Manifold.riemannianEDist I q (v t)).toReal) ^ 2)
      =ᶠ[𝓝 (0:ℝ)]
      (fun t : ℝ => ‖(show TangentSpace I q from
        ψ ((extChartAt I (GExp (cov := cov) hmet q U)) (v t)))‖ ^ 2) := by
    filter_upwards [hdist_eq] with t ht
    rw [ht]
  exact (hnorm2.congr_deriv hval).congr_of_eventuallyEq hfun

end Work.OddBound.polygon
