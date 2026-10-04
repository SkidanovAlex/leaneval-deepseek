import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal
import Submission.GExpSmooth
import Submission.XuMain
import Submission.ConjEnergy
import Submission.Work.OddBound.polygon.minimisers_cluster_near_segmentDomain
import Submission.Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt
import Submission.Work.OddBound.sqDistChart.minimisers_cluster_chartCoord
import Submission.Work.OddBound.polygonValue.edist_eq_ofReal_riemannianDist

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000


open scoped Manifold in
private theorem mfderiv_eq_fderiv_v434 {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {f : E' → F'} {x : E'} :
    (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, F') f x : E' →L[ℝ] F') = fderiv ℝ f x := by
  rw [mfderiv_eq_fderiv]
  first | rfl | (ext v; rfl) | simp

namespace Work.OddBound.sqDistChart

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

noncomputable section

/-- The chart frame as a map into the total space of the tangent bundle is `C^∞` in the base
point and the (chart) vector. -/
lemma contMDiffAt_frameVector_total (z : M) {q₀ : M} {a₀ : E}
    (hq₀ : q₀ ∈ (extChartAt I z).source) :
    ContMDiffAt (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × E => (⟨p.1, Submission.Geodesic.frameVector (I := I) z p.1 p.2⟩ : TangentBundle I M))
      (q₀, a₀) := by
  have hbase : q₀ ∈ (trivializationAt E (TangentSpace I) z).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; simpa only [extChartAt_source] using hq₀
  have hsrc : (⟨q₀, Submission.Geodesic.frameVector (I := I) z q₀ a₀⟩ : TangentBundle I M) ∈
      (trivializationAt E (TangentSpace I) z).source :=
    Trivialization.mem_source _ |>.mpr hbase
  refine ((trivializationAt E (TangentSpace I) z).contMDiffAt_iff
    (f := fun p : M × E => (⟨p.1, Submission.Geodesic.frameVector (I := I) z p.1 p.2⟩ : TangentBundle I M))
    (x₀ := (q₀, a₀)) hsrc).mpr ⟨contMDiffAt_fst, ?_⟩
  have hnb : {p : M × E | p.1 ∈ (extChartAt I z).source} ∈ 𝓝 (q₀, a₀) :=
    (isOpen_extChartAt_source (I := I) z).preimage continuous_fst |>.mem_nhds hq₀
  refine contMDiffAt_snd.congr_of_eventuallyEq ?_
  filter_upwards [hnb] with p hp
  have hb : p.1 ∈ (trivializationAt E (TangentSpace I) z).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; simpa only [extChartAt_source] using hp
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ
    (e := trivializationAt E (TangentSpace I) z) hb]
  exact Submission.GExpFlow.clm_frameVector (I := I) hp p.2

/-- The chart coordinates of `GExp` (joint in the base point and the chart velocity) are `C^∞`
at the base configuration, composed with the inverse chart at `x₀`. -/
lemma contMDiffAt_chartGExp_chartCoords (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {z x₀ y₀ : M} {s₀ : E} {w : TangentSpace I x₀}
    (hG : ContMDiffAt (I.prod 𝓘(ℝ,E)) I ∞ (fun p : M × E => GExp (cov := cov) hmet p.1
      (Submission.Geodesic.frameVector (I := I) z p.1 p.2)) (x₀, s₀))
    (hs₀ : Submission.Geodesic.frameVector (I := I) z x₀ s₀ = w)
    (hw : GExp (cov := cov) hmet x₀ w = y₀) :
    ContMDiffAt 𝓘(ℝ,E×E) 𝓘(ℝ,E) ∞
      (fun p : E × E => (extChartAt I y₀) (GExp (cov := cov) hmet ((extChartAt I x₀).symm p.1)
        (Submission.Geodesic.frameVector (I := I) z ((extChartAt I x₀).symm p.1) p.2)))
      ((extChartAt I x₀) x₀, s₀) := by
  set u₀ : E := (extChartAt I x₀) x₀ with hu₀def
  have hsq : (extChartAt I x₀).symm u₀ = x₀ := by
    rw [hu₀def]; exact (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)
  have htgt : (extChartAt I x₀).target ∈ 𝓝 ((extChartAt I x₀) x₀) := by
    have h : IsOpen (extChartAt I x₀).target := OpenPartialHomeomorph.isOpen_extend_target _ (I := I)
    exact h.mem_nhds (mem_extChartAt_target x₀)
  have hfst : ContMDiffAt 𝓘(ℝ,E×E) 𝓘(ℝ,E) ∞ (fun p : E × E => p.1) ((extChartAt I x₀) x₀, s₀) :=
    (ContinuousLinearMap.fst ℝ E E).contMDiffAt
  have hsnd : ContMDiffAt 𝓘(ℝ,E×E) 𝓘(ℝ,E) ∞ (fun p : E × E => p.2) ((extChartAt I x₀) x₀, s₀) :=
    (ContinuousLinearMap.snd ℝ E E).contMDiffAt
  have hA1 : ContMDiffAt 𝓘(ℝ,E×E) I ∞ (fun p : E × E => (extChartAt I x₀).symm p.1)
      ((extChartAt I x₀) x₀, s₀) :=
    ((contMDiffOn_extChartAt_symm (I := I) x₀).contMDiffAt htgt).comp
      ((extChartAt I x₀) x₀, s₀) hfst
  have hA : ContMDiffAt 𝓘(ℝ,E×E) (I.prod 𝓘(ℝ,E)) ∞
      (fun p : E × E => ((extChartAt I x₀).symm p.1, p.2)) ((extChartAt I x₀) x₀, s₀) :=
    hA1.prodMk hsnd
  have hC : ContMDiffAt I 𝓘(ℝ,E) ∞ (extChartAt I y₀) y₀ :=
    (contMDiffOn_extChartAt (I := I) (x := y₀) (n := ∞)).contMDiffAt
      ((chartAt H y₀).open_source.mem_nhds (mem_chart_source H y₀))
  have hG' : ContMDiffAt (I.prod 𝓘(ℝ,E)) I ∞ (fun p : M × E => GExp (cov := cov) hmet p.1
      (Submission.Geodesic.frameVector (I := I) z p.1 p.2)) ((extChartAt I x₀).symm u₀, s₀) := by
    rw [hsq]; exact hG
  have hval : GExp (cov := cov) hmet ((extChartAt I x₀).symm u₀)
      (Submission.Geodesic.frameVector (I := I) z ((extChartAt I x₀).symm u₀) s₀) = y₀ := by
    rw [hsq, hs₀]; exact hw
  have hC' : ContMDiffAt I 𝓘(ℝ,E) ∞ (extChartAt I y₀)
      (GExp (cov := cov) hmet ((extChartAt I x₀).symm u₀)
        (Submission.Geodesic.frameVector (I := I) z ((extChartAt I x₀).symm u₀) s₀)) := by
    rw [hval]; exact hC
  have key := hG'.comp (u₀, s₀) hA
  have key2 := hC'.comp (u₀, s₀) key
  simpa only [Function.comp_def, hu₀def] using key2

/-- **Invertibility of the differential of `GExp x₀` at a vector below the injectivity radius.** -/
lemma isInvertible_mfderiv_GExp_of_norm_lt (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0) {x₀ : M} {w : TangentSpace I x₀} {r : ℝ}
    (hinj : Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x₀ r)
    (hwlt : ‖w‖ < r) :
    (mfderiv% (fun v : E => GExp (cov := cov) hmet x₀ v) (show E from w)).IsInvertible := by
  rcases eq_or_ne w 0 with h0 | h0
  · subst h0
    have hz : (mfderiv% (fun v : E => GExp (cov := cov) hmet x₀ v) (show E from (0 : TangentSpace I x₀)))
        = ContinuousLinearMap.id ℝ E := by
      rw [show (show E from (0 : TangentSpace I x₀)) = (0 : E) from rfl]
      exact Submission.GExpLocalInj.mfderiv_GExp_zero (cov := cov) hmet x₀
    rw [hz]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  · exact Submission.ConjEnergy.isInvertible_mfderiv_of_mem_segmentDomain (cov := cov) hmet htor
      (Submission.SegmentDomain.ball_subset_segmentDomain (I := I) (cov := cov) hmet htor hinj
        (by rw [Metric.mem_ball, dist_zero_right]; exact hwlt)) h0

/-- **Invertibility of the slice derivative of the chart model of the exponential map.** -/
lemma isInvertible_fderiv_slice (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {z x₀ y₀ : M} {w : TangentSpace I x₀} (hz : x₀ ∈ (extChartAt I z).source)
    (hw : GExp (cov := cov) hmet x₀ w = y₀) {s₀ : E}
    (hs₀ : Submission.Geodesic.frameVector (I := I) z x₀ s₀ = w)
    (hinv : (mfderiv% (fun v : E => GExp (cov := cov) hmet x₀ v)
      (show E from w)).IsInvertible) :
    (fderiv ℝ (fun s : E => (extChartAt I y₀) (GExp (cov := cov) hmet x₀
      (Submission.Geodesic.frameVector (I := I) z x₀ s))) s₀).IsInvertible := by
  set L : E →L[ℝ] E := (trivializationAt E (TangentSpace I) z).symmL ℝ x₀ with hLdef
  have hLs : ∀ s : E, L s = Submission.Geodesic.frameVector (I := I) z x₀ s := fun s => rfl
  have hL₀ : L s₀ = (show E from w) := by rw [hLs, hs₀]
  have hLind : L.IsInvertible := by
    rw [hLdef]
    have hx : x₀ ∈ (trivializationAt E (TangentSpace I) z).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; simpa only [extChartAt_source] using hz
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (f := (trivializationAt E (TangentSpace I) z).symmL ℝ x₀)
      (g := (trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ x₀) ?_ ?_
    · ext s
      simpa using Trivialization.symmL_continuousLinearMapAt (R := ℝ)
        (trivializationAt E (TangentSpace I) z) hx s
    · ext V
      simpa using Trivialization.continuousLinearMapAt_symmL (R := ℝ)
        (trivializationAt E (TangentSpace I) z) hx V
  set Gfun : E → M := fun v => GExp (cov := cov) hmet x₀ v with hGfundef
  set hh : E → E := fun v => (extChartAt I y₀) (Gfun v) with hhhdef
  have hfun : (fun s : E => (extChartAt I y₀) (GExp (cov := cov) hmet x₀
      (Submission.Geodesic.frameVector (I := I) z x₀ s)))
      = fun s : E => hh (L s) := by
    funext s; rw [hhhdef, hGfundef, hLs]
  rw [hfun]
  have h1 : MDifferentiableAt 𝓘(ℝ, E) I Gfun (show E from w) := by
    rw [hGfundef]
    exact (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet x₀ w).mdifferentiableAt
      (by norm_num)
  have h2 : MDifferentiableAt I 𝓘(ℝ, E) (fun z : M => (extChartAt I y₀) z) (Gfun (show E from w)) := by
    change MDifferentiableAt I 𝓘(ℝ, E) (fun z : M => (extChartAt I y₀) z)
      (GExp (cov := cov) hmet x₀ w)
    rw [hw]
    exact ((contMDiffOn_extChartAt (I := I) (x := y₀) (n := ∞)).contMDiffAt
      ((chartAt H y₀).open_source.mem_nhds (mem_chart_source H y₀))).mdifferentiableAt (by norm_num)
  have hmdhh : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) hh (show E from w) := by
    rw [hhhdef]
    exact h2.comp (show E from w) h1
  have hhhdiff : DifferentiableAt ℝ hh (L s₀) := by
    rw [hL₀]
    exact mdifferentiableAt_iff_differentiableAt.mp hmdhh
  have hfdhh : fderiv ℝ hh (show E from w) = (mfderiv% Gfun (show E from w)) := by
    erw [← mfderiv_eq_fderiv_v434]
    change mfderiv% ((fun z : M => (extChartAt I y₀) z) ∘ Gfun) (show E from w)
      = mfderiv% Gfun (show E from w)
    rw [mfderiv_comp (I := 𝓘(ℝ,E)) (I' := I) (I'' := 𝓘(ℝ,E)) (x := (show E from w))
      (f := Gfun) (g := fun z : M => (extChartAt I y₀) z) h2 h1]
    change (mfderiv% (fun z : M => (extChartAt I y₀) z) (Gfun (show E from w))) ∘SL
      (mfderiv% Gfun (show E from w)) = mfderiv% Gfun (show E from w)
    rw [show Gfun (show E from w) = y₀ from hw]
    rw [mfderiv_extChartAt_self]
    rw [show ContinuousLinearMap.id ℝ (TangentSpace I y₀) = (ContinuousLinearMap.id ℝ E : E →L[ℝ] E)
      from rfl]
    exact ContinuousLinearMap.id_comp _
  have hcomp_eq : fderiv ℝ (fun s : E => hh (L s)) s₀
      = (fderiv ℝ hh (L s₀)) ∘SL (fderiv ℝ L s₀) := by
    rw [show (fun s : E => hh (L s)) = hh ∘ ⇑L from rfl]
    rw [fderiv_comp s₀ hhhdiff L.differentiableAt]
  rw [hcomp_eq, hL₀, L.fderiv, hfdhh]
  exact ContinuousLinearMap.IsInvertible.comp hinv hLind

/-- **Joint smoothness of the chart metric (quadratic form)** in the base point and the coordinate
vector: `(q, a) ↦ chartGram x₀ q a a` is `C^∞` at `(p₀, a₀)` for `p₀` in the chart at `x₀`.
(Proved in coordinates using a basis, like `Submission.ChartBounds.continuousAt_chartGram_prod`.) -/
lemma contMDiffAt_chartGram_prod (x₀ : M) {p₀ : M} (hp₀ : p₀ ∈ (chartAt H x₀).source) (a₀ : E) :
    ContMDiffAt (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun q : M × E => Submission.ChartConnection.chartGram (I := I) x₀ q.1 q.2 q.2) (p₀, a₀) := by
  obtain bb : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  have hfun : (fun q : M × E => Submission.ChartConnection.chartGram (I := I) x₀ q.1 q.2 q.2)
      = fun q : M × E => ∑ i, ∑ j, (bb.repr q.2 i) * (bb.repr q.2 j)
          * Submission.ChartConnection.chartGram (I := I) x₀ q.1 (bb i) (bb j) := by
    funext q
    exact Submission.ChartBounds.chartGram_eq_sum_repr (I := I) bb x₀ q.1 q.2 q.2
  rw [hfun]
  refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
  have hsnd : ContMDiffAt (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ (fun q : M × E => q.2) (p₀, a₀) :=
    contMDiffAt_snd
  have hcoord : ∀ k : Fin (Module.finrank ℝ E), ContMDiffAt (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun q : M × E => bb.repr q.2 k) (p₀, a₀) := by
    intro k
    have hL : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun v : E => bb.repr v k) a₀ := by
      have hclm : ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (bb.coord k)) : E →L[ℝ] ℝ)
          = fun v => bb.repr v k := by
        ext v; exact Module.Basis.coord_apply bb k v
      rw [← hclm]
      exact (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (bb.coord k)).contMDiffAt
    exact ContMDiffAt.comp (p₀, a₀) hL hsnd
  have hgram : ContMDiffAt (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun q : M × E => Submission.ChartConnection.chartGram (I := I) x₀ q.1 (bb i) (bb j))
      (p₀, a₀) :=
    ContMDiffAt.comp (p₀, a₀) (Submission.Distance.contMDiffAt_chartGram (I := I) x₀ (bb i) (bb j) hp₀)
      contMDiffAt_fst
  refine (((hcoord i).mul (hcoord j)).mul hgram).congr_of_eventuallyEq ?_
  filter_upwards with q
  simp only [Pi.mul_apply]

end

theorem sqDist_contDiffAt_charts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x₀ y₀ : M} {r : ℝ} (hr : 0 < r)
    (hinj : ∀ u v : TangentSpace I x₀, ‖u‖ < r → ‖v‖ < r →
      Submission.GlobalExp.GExp (cov := cov) hmet x₀ u
        = Submission.GlobalExp.GExp (cov := cov) hmet x₀ v → u = v)
    (hd : Submission.Distance.riemannianDist (I := I) x₀ y₀ < r)
    {w : TangentSpace I x₀} (hw : Submission.GlobalExp.GExp (cov := cov) hmet x₀ w = y₀)
    (hwn : ‖w‖ = Submission.Distance.riemannianDist (I := I) x₀ y₀) :
    ContDiffAt ℝ 2 (fun uv : E × E =>
      (Submission.Distance.riemannianDist (I := I)
        ((extChartAt I x₀).symm uv.1) ((extChartAt I y₀).symm uv.2)) ^ 2)
      ((extChartAt I x₀) x₀, (extChartAt I y₀) y₀) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  -- ## 0. the finite atlas and the chart data
  obtain ⟨n, z, Z, hZc, hZsrc, hcov⟩ :=
    Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt (I := I) (M := M)
  obtain ⟨δat, hδat, hbaseat⟩ :=
    Submission.GExpSmooth.exists_pos_smoothOnBall (cov := cov) hmet z Z hZc hZsrc hcov
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ x₀))
  set zz : M := z i with hzzdef
  have hzsrc : x₀ ∈ (extChartAt I zz).source := by
    rw [extChartAt_source]; exact hZsrc i hxi
  -- ## 1. the chart velocity of `w`
  set s₀ : E := (trivializationAt E (TangentSpace I) zz).continuousLinearMapAt ℝ x₀ w with hs₀def
  have hframe_s₀ : Submission.Geodesic.frameVector (I := I) zz x₀ s₀ = w := by
    rw [hs₀def]
    exact Submission.GExpFlow.frameVector_clm (I := I) hzsrc w
  set u₀ : E := (extChartAt I x₀) x₀ with hu₀def
  set t₀ : E := (extChartAt I y₀) y₀ with ht₀def
  -- ## 2. joint smoothness of the `GExp` family at `(x₀, s₀)`
  have hG : ContMDiffAt (I.prod 𝓘(ℝ,E)) I ∞ (fun p : M × E => GExp (cov := cov) hmet p.1
      (Submission.Geodesic.frameVector (I := I) zz p.1 p.2)) (x₀, s₀) := by
    have h := Submission.GExpSmooth.contMDiffAt_gexpChart_all (cov := cov) hmet z Z hZsrc hcov
      δat hδat hbaseat i x₀ s₀ hxi
    change ContMDiffAt (I.prod 𝓘(ℝ,E)) I ∞ (fun p : M × E => GExp (cov := cov) hmet p.1
      (Submission.Geodesic.frameVector (I := I) (z i) p.1 p.2)) (x₀, s₀) at h
    simpa only [← hzzdef] using h
  -- ## 3. the chart model `γ` and its smoothness
  set γ : E × E → E := fun p => (extChartAt I y₀) (GExp (cov := cov) hmet ((extChartAt I x₀).symm p.1)
      (Submission.Geodesic.frameVector (I := I) zz ((extChartAt I x₀).symm p.1) p.2)) with hγdef
  have hγ : ContMDiffAt 𝓘(ℝ,E×E) 𝓘(ℝ,E) ∞ γ (u₀, s₀) := by
    have h := contMDiffAt_chartGExp_chartCoords (cov := cov) hmet hG hframe_s₀ hw
    simpa only [hγdef, hu₀def] using h
  have hγd : ContDiffAt ℝ ∞ γ (u₀,s₀) := contMDiffAt_iff_contDiffAt.mp hγ
  -- ## 4. the implicit equation `f`
  set f : (E×E) × E → E := fun p => γ (p.1.1, p.2) - p.1.2 with hfdef
  have hf_smooth : ContDiffAt ℝ ∞ f ((u₀,t₀),s₀) := by
    have hLmd : ContMDiffAt 𝓘(ℝ,(E×E)×E) 𝓘(ℝ,E×E) ∞
        (fun p : (E×E)×E => (p.1.1, p.2)) ((u₀,t₀),s₀) :=
      (((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ (E×E) E)).prod
        (ContinuousLinearMap.snd ℝ (E×E) E)).contMDiffAt
    have hL : ContDiffAt ℝ ∞ (fun p : (E×E)×E => (p.1.1, p.2)) ((u₀,t₀),s₀) :=
      contMDiffAt_iff_contDiffAt.mp hLmd
    have h1' : ContDiffAt ℝ ∞ (γ ∘ (fun p : (E×E)×E => (p.1.1, p.2))) ((u₀,t₀),s₀) :=
      hγd.comp ((u₀,t₀),s₀) hL
    have h1 : ContDiffAt ℝ ∞ (fun p : (E×E)×E => γ (p.1.1, p.2)) ((u₀,t₀),s₀) := h1'
    have h2 : ContDiffAt ℝ ∞ (fun p : (E×E)×E => p.1.2) ((u₀,t₀),s₀) :=
      contDiffAt_snd.comp ((u₀,t₀),s₀) contDiffAt_fst
    rw [hfdef]
    exact h1.sub h2
  -- ## 5. invertibility of the slice derivative
  have hwn' : ‖w‖ < r := by rw [hwn]; exact hd
  have hinv : (mfderiv% (fun v : E => GExp (cov := cov) hmet x₀ v) (show E from w)).IsInvertible :=
    isInvertible_mfderiv_GExp_of_norm_lt (cov := cov) hmet htor hinj hwn'
  have hslice0 : (fderiv ℝ (fun s : E => (extChartAt I y₀) (GExp (cov := cov) hmet x₀
      (Submission.Geodesic.frameVector (I := I) zz x₀ s))) s₀).IsInvertible :=
    isInvertible_fderiv_slice (cov := cov) hmet hzsrc hw hframe_s₀ hinv
  have hslice : (fderiv ℝ (fun s : E => γ (u₀, s)) s₀).IsInvertible := by
    have hfun : (fun s : E => γ (u₀, s)) = fun s : E => (extChartAt I y₀)
        (GExp (cov := cov) hmet x₀ (Submission.Geodesic.frameVector (I := I) zz x₀ s)) := by
      funext s
      rw [hγdef, hu₀def]
      dsimp only
      rw [(extChartAt I x₀).left_inv (mem_extChartAt_source x₀)]
    rw [hfun]; exact hslice0
  have hiff : DifferentiableAt ℝ f ((u₀,t₀),s₀) := hf_smooth.differentiableAt (by norm_num)
  have hif2 : (fderiv ℝ f ((u₀,t₀),s₀) ∘SL ContinuousLinearMap.inr ℝ (E × E) E).IsInvertible := by
    have hdg : DifferentiableAt ℝ (fun s : E => ((u₀,t₀), s)) s₀ := by fun_prop
    have hcomp := (hiff.hasFDerivAt.comp s₀
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) (u₀,t₀) s₀))
    have hinr : (fderiv ℝ f ((u₀,t₀),s₀)) ∘SL (ContinuousLinearMap.inr ℝ (E×E) E)
        = fderiv ℝ (fun s : E => γ (u₀, s)) s₀ := by
      rw [← hcomp.fderiv]
      change fderiv ℝ (fun s : E => f ((u₀,t₀), s)) s₀ = fderiv ℝ (fun s : E => γ (u₀, s)) s₀
      have hse : (fun s : E => f ((u₀,t₀), s)) = fun s : E => γ (u₀, s) - t₀ := by
        funext s; rw [hfdef]
      rw [hse, fderiv_sub_const]
    rw [hinr]; exact hslice
  -- ## 6. the implicit function `ψ` and its properties
  set ψ : E × E → E := hf_smooth.implicitFunction (by norm_num) hif2 with hψdef
  have hψ_smooth : ContDiffAt ℝ ∞ ψ (u₀, t₀) :=
    ContDiffAt.contDiffAt_implicitFunction hf_smooth (by norm_num) hif2
  have hψ_self : ψ (u₀,t₀) = s₀ :=
    ContDiffAt.implicitFunction_apply_self hf_smooth (by norm_num) hif2
  have hfbase : f ((u₀,t₀),s₀) = 0 := by
    rw [hfdef, hγdef, hu₀def, ht₀def]
    dsimp only
    rw [(extChartAt I x₀).left_inv (mem_extChartAt_source x₀), hframe_s₀, hw]
    simp
  have hψeq : ∀ᶠ p in 𝓝 (u₀, t₀), γ (p.1, ψ p) = p.2 := by
    have h := ContDiffAt.eventually_apply_implicitFunction hf_smooth (by norm_num) hif2
    filter_upwards [h] with p hp
    have hp0 : f (p, ψ p) = 0 := by rw [hfbase] at hp; exact hp
    have hval : f (p, ψ p) = γ (p.1, ψ p) - p.2 := by rw [hfdef]
    rw [hval] at hp0
    exact sub_eq_zero.mp hp0
  have hψuniq : ∀ᶠ v in 𝓝 (((u₀,t₀),s₀)), (γ (v.1.1, v.2) = v.1.2 ↔ ψ v.1 = v.2) := by
    have h := ContDiffAt.eventually_apply_eq_iff_implicitFunction hf_smooth (by norm_num) hif2
    filter_upwards [h] with v hv
    have hv0 : f v = 0 ↔ ψ v.1 = v.2 := by rw [hfbase] at hv; exact hv
    have hval : f v = γ (v.1.1, v.2) - v.1.2 := by rw [hfdef]
    rw [hval] at hv0
    constructor
    · intro hg
      exact hv0.mp (sub_eq_zero.mpr hg)
    · intro hg
      exact sub_eq_zero.mp (hv0.mpr hg)
  -- ## 7. the distance identity
  have hdist : ∀ᶠ p : E × E in 𝓝 (u₀, t₀),
      (Submission.Distance.riemannianDist (I := I) ((extChartAt I x₀).symm p.1)
        ((extChartAt I y₀).symm p.2)) ^ 2
        = ‖Submission.Geodesic.frameVector (I := I) zz ((extChartAt I x₀).symm p.1) (ψ p)‖ ^ 2 := by
    -- split the uniqueness statement into a product neighbourhood
    have hψuniq' : ∀ᶠ v in (𝓝 (u₀, t₀)) ×ˢ (𝓝 s₀), (γ (v.1.1, v.2) = v.1.2 ↔ ψ v.1 = v.2) := by
      rw [← nhds_prod_eq]; exact hψuniq
    obtain ⟨A, hA, B, hB, hAB⟩ := Filter.eventually_prod_iff.mp hψuniq'
    obtain ⟨δB, hδB, hballB⟩ : ∃ δB > 0, ∀ a : E, a ∈ Metric.ball s₀ δB → B a := by
      obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hB
      exact ⟨δ, hδ, fun a ha => hsub ha⟩
    have hd_edist : Manifold.riemannianEDist I x₀ y₀ < ENNReal.ofReal r := by
      rw [Work.OddBound.polygonValue.edist_eq_ofReal_riemannianDist (I := I) x₀ y₀]
      exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hd
    have hwn_edist : Manifold.riemannianEDist I x₀ y₀ = ENNReal.ofReal ‖w‖ := by
      rw [Work.OddBound.polygonValue.edist_eq_ofReal_riemannianDist (I := I) x₀ y₀]
      rw [hwn]
    obtain ⟨εc, hεc, hcluster⟩ := minimisers_cluster_chartCoord (cov := cov) hmet htor hzsrc hinj
      hd_edist hw hwn_edist (δ := δB) hδB
    -- continuity of the two chart inverses
    have htgtX : (extChartAt I x₀).target ∈ 𝓝 u₀ := by
      rw [hu₀def]
      exact (OpenPartialHomeomorph.isOpen_extend_target (chartAt H x₀) (I := I)).mem_nhds
        (mem_extChartAt_target x₀)
    have htgtY : (extChartAt I y₀).target ∈ 𝓝 t₀ := by
      rw [ht₀def]
      exact (OpenPartialHomeomorph.isOpen_extend_target (chartAt H y₀) (I := I)).mem_nhds
        (mem_extChartAt_target y₀)
    have hfst : ContinuousAt (fun p : E×E => p.1) ((u₀,t₀) : E×E) := continuousAt_fst
    have hsnd : ContinuousAt (fun p : E×E => p.2) ((u₀,t₀) : E×E) := continuousAt_snd
    have hcontx : ContinuousAt (fun p : E×E => (extChartAt I x₀).symm p.1) (u₀,t₀) := by
      have hout : ContinuousAt (extChartAt I x₀).symm ((fun p : E×E => p.1) ((u₀,t₀) : E×E)) := by
        change ContinuousAt (extChartAt I x₀).symm u₀
        rw [hu₀def]
        exact ((contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀).contMDiffAt htgtX).continuousAt
      exact ContinuousAt.comp hout hfst
    have hconty : ContinuousAt (fun p : E×E => (extChartAt I y₀).symm p.2) (u₀,t₀) := by
      have hout : ContinuousAt (extChartAt I y₀).symm ((fun p : E×E => p.2) ((u₀,t₀) : E×E)) := by
        change ContinuousAt (extChartAt I y₀).symm t₀
        rw [ht₀def]
        exact ((contMDiffOn_extChartAt_symm (I := I) (n := ∞) y₀).contMDiffAt htgtY).continuousAt
      exact ContinuousAt.comp hout hsnd
    have hx_ev : ∀ᶠ p : E×E in 𝓝 (u₀,t₀),
        Manifold.riemannianEDist I x₀ ((extChartAt I x₀).symm p.1) < ENNReal.ofReal εc := by
      have h1 : Tendsto (fun p : E×E => (extChartAt I x₀).symm p.1) (𝓝 (u₀,t₀)) (𝓝 x₀) := by
        have h := hcontx.tendsto
        convert h using 2
        change x₀ = (extChartAt I x₀).symm u₀
        rw [hu₀def]
        exact ((extChartAt I x₀).left_inv (mem_extChartAt_source x₀)).symm
      exact h1.eventually (eventually_riemannianEDist_lt (I := I) x₀
        (ENNReal.ofReal_pos.mpr hεc))
    have hy_ev : ∀ᶠ p : E×E in 𝓝 (u₀,t₀),
        Manifold.riemannianEDist I y₀ ((extChartAt I y₀).symm p.2) < ENNReal.ofReal εc := by
      have h1 : Tendsto (fun p : E×E => (extChartAt I y₀).symm p.2) (𝓝 (u₀,t₀)) (𝓝 y₀) := by
        have h := hconty.tendsto
        convert h using 2
        change y₀ = (extChartAt I y₀).symm t₀
        rw [ht₀def]
        exact ((extChartAt I y₀).left_inv (mem_extChartAt_source y₀)).symm
      exact h1.eventually (eventually_riemannianEDist_lt (I := I) y₀
        (ENNReal.ofReal_pos.mpr hεc))
    have hsrc_ev : ∀ᶠ p : E×E in 𝓝 (u₀,t₀), (extChartAt I x₀).symm p.1 ∈ (extChartAt I zz).source := by
      have hsrc_nhds : (extChartAt I zz).source ∈ 𝓝 ((extChartAt I x₀).symm ((fun p : E×E => p.1) ((u₀,t₀) : E×E))) := by
        have hpt : (extChartAt I x₀).symm ((fun p : E×E => p.1) ((u₀,t₀) : E×E)) = x₀ := by
          change (extChartAt I x₀).symm u₀ = x₀
          rw [hu₀def]
          exact (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)
        rw [hpt]
        exact (isOpen_extChartAt_source (I := I) zz).mem_nhds hzsrc
      exact hcontx.eventually hsrc_nhds
    have htgt_ev : ∀ᶠ p : E×E in 𝓝 (u₀,t₀), p.2 ∈ (extChartAt I y₀).target := by
      have h1 : (extChartAt I y₀).target ∈ 𝓝 ((fun p : E×E => p.2) ((u₀,t₀) : E×E)) := by
        change (extChartAt I y₀).target ∈ 𝓝 t₀
        exact htgtY
      exact hsnd.eventually h1
    filter_upwards [hA, hx_ev, hy_ev, hsrc_ev, htgt_ev] with p hpA hpx hpy hsrc htgt
    set x : M := (extChartAt I x₀).symm p.1 with hxdef
    set y : M := (extChartAt I y₀).symm p.2 with hydef
    -- a minimising vector and its chart coordinate
    obtain ⟨V, hVexp, hVnorm⟩ := Submission.HopfRinow.exists_geodesic_riemannianEDist_eq
      (I := I) (cov := cov) hmet htor x y
    have hcl := hcluster x (by rw [hxdef]; exact hpx) y (by rw [hydef]; exact hpy) V
      (by rw [hxdef]; exact hsrc) hVexp hVnorm
    set W : E := (trivializationAt E (TangentSpace I) zz).continuousLinearMapAt ℝ x V with hWdef
    have hclm_s₀ : (trivializationAt E (TangentSpace I) zz).continuousLinearMapAt ℝ x₀ w = s₀ :=
      hs₀def.symm
    have hnrm : ‖W - s₀‖ < δB := by
      have h2 : ‖(trivializationAt E (TangentSpace I) zz).continuousLinearMapAt ℝ x V
          - (trivializationAt E (TangentSpace I) zz).continuousLinearMapAt ℝ x₀ w‖ < δB := hcl
      rw [hclm_s₀] at h2
      exact h2
    have hWB : B W := hballB W (by rw [Metric.mem_ball, dist_eq_norm]; exact hnrm)
    -- the value of `γ` at `(p.1, W)`
    have hclmV : Submission.Geodesic.frameVector (I := I) zz x W = V := by
      rw [hWdef]
      exact Submission.GExpFlow.frameVector_clm (I := I) (by rw [hxdef]; exact hsrc) V
    have hγ_val : γ (p.1, W) = p.2 := by
      rw [hγdef]
      dsimp only
      rw [← hxdef, hclmV, hVexp, hydef, (extChartAt I y₀).right_inv htgt]
    have hψval : ψ p = W := (hAB hpA hWB).mp hγ_val
    -- conclude
    have hrd : Submission.Distance.riemannianDist (I := I) x y
        = ‖Submission.Geodesic.frameVector (I := I) zz x (ψ p)‖ := by
      rw [Work.OddBound.polygon.riemannianDist_eq_toReal, hVnorm,
        ENNReal.toReal_ofReal (norm_nonneg V), ← hclmV, ← hψval]
    rw [hrd]
  -- ## 8. smoothness of the chart model of the squared distance
  have hSig : ContDiffAt ℝ 2 (fun p : E × E => ‖Submission.Geodesic.frameVector (I := I) zz
      ((extChartAt I x₀).symm p.1) (ψ p)‖ ^ 2) (u₀,t₀) := by
    have hpt_s : ((extChartAt I x₀).symm u₀, ψ (u₀,t₀)) = (x₀, s₀) := by
      rw [show (extChartAt I x₀).symm u₀ = x₀ from by
        rw [hu₀def]; exact (extChartAt I x₀).left_inv (mem_extChartAt_source x₀), hψ_self]
    have htgtX2 : (extChartAt I x₀).target ∈ 𝓝 u₀ := by
      rw [hu₀def]
      exact (OpenPartialHomeomorph.isOpen_extend_target (chartAt H x₀) (I := I)).mem_nhds
        (mem_extChartAt_target x₀)
    have hfst_md : ContMDiffAt 𝓘(ℝ,E×E) 𝓘(ℝ,E) ∞ (fun p : E×E => p.1) (u₀,t₀) :=
      (ContinuousLinearMap.fst ℝ E E).contMDiffAt
    have hin1 : ContMDiffAt 𝓘(ℝ,E×E) I ∞ (fun p : E×E => (extChartAt I x₀).symm p.1) (u₀,t₀) := by
      have hout : ContMDiffAt 𝓘(ℝ,E) I ∞ (extChartAt I x₀).symm ((fun p : E×E => p.1) (u₀,t₀)) := by
        change ContMDiffAt 𝓘(ℝ,E) I ∞ (extChartAt I x₀).symm u₀
        rw [hu₀def]
        exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀).contMDiffAt htgtX2
      exact ContMDiffAt.comp ((u₀,t₀) : E×E) hout hfst_md
    have hψmd : ContMDiffAt 𝓘(ℝ,E×E) 𝓘(ℝ,E) ∞ ψ (u₀,t₀) := hψ_smooth.contMDiffAt
    have hA : ContMDiffAt 𝓘(ℝ,E×E) (I.prod 𝓘(ℝ,E)) ∞
        (fun p : E×E => ((extChartAt I x₀).symm p.1, ψ p)) (u₀,t₀) := hin1.prodMk hψmd
    have hchart : ContMDiffAt (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
        (fun q : M × E => Submission.ChartConnection.chartGram (I := I) zz q.1 q.2 q.2) (x₀, s₀) :=
      contMDiffAt_chartGram_prod (I := I) zz (by simpa only [extChartAt_source] using hzsrc) s₀
    have hchart' : ContMDiffAt (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
        (fun q : M × E => Submission.ChartConnection.chartGram (I := I) zz q.1 q.2 q.2)
        ((extChartAt I x₀).symm u₀, ψ (u₀,t₀)) := by
      rw [hpt_s]; exact hchart
    have hcomp2 := ContMDiffAt.comp ((u₀,t₀) : E×E) hchart' hA
    have hcd2 : ContDiffAt ℝ ∞ (fun p : E×E => Submission.ChartConnection.chartGram (I := I) zz
        ((extChartAt I x₀).symm p.1) (ψ p) (ψ p)) (u₀,t₀) := contMDiffAt_iff_contDiffAt.mp hcomp2
    refine (hcd2.of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from by decide)).congr_of_eventuallyEq ?_
    filter_upwards with p
    have hnn : 0 ≤ Submission.ChartConnection.chartGram (I := I) zz ((extChartAt I x₀).symm p.1)
        (ψ p) (ψ p) := by
      rw [Submission.ChartConnection.chartGram_apply, real_inner_self_eq_norm_sq]
      exact sq_nonneg _
    rw [Submission.GExpFlow.norm_frameVector, Real.sq_sqrt hnn]
  exact hSig.congr_of_eventuallyEq hdist

end Work.OddBound.sqDistChart
