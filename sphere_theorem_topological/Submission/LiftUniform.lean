import Submission.LiftLemma
import Submission.GExpRay2
import Submission.XuMain
import Submission.GExpJoint
import Submission.GExpFlow

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.GlobalExp
open Submission.InjRadius
open Submission.ChartConnection
open Submission.GExpFlow

/-!
# Uniform continuity of the inverse of the exponential map

`Submission.XuMain.exists_pos_edist_lt_imp_norm_sub_lt` is the *pointwise* statement that the inverse
of `GExp p` (restricted to the segment domain) is continuous: at every `v ∈ D̃_p`, points close to
`GExp p v` have segment-domain preimages close to `v`.

The lifting arguments of Klingenberg's estimate need the **uniform** form: on the whole closed ball
of radius `ρ' < inj(p)` the modulus of continuity can be taken uniform, and moreover *uniformly in the
base point*.  This module proves

* `exists_pos_forall_edist_lt_imp_norm_lt` — the uniform form for a fixed base point `p`
  (a compactness upgrade of `exists_pos_edist_lt_imp_norm_sub_lt`), stated in the fibre norm;
* `exists_pos_forall_frameVector_edist_lt_imp_norm_sub_lt` — the chart-coordinate form, **uniform
  over a compact chart piece** `Z` (same base point `q ∈ Z`);
* `exists_pos_joint_frameVector_edist_lt_imp_norm_sub_lt` — the **joint** form, where the two base
  points may differ inside `Z` (this is what the parametric lifting argument consumes);
* `exists_pos_forall_edist_lt_imp_norm_sub_lt_of_chart` — the **fibre-norm** form, uniform over a
  compact chart piece (base points varying, conclusion in the Riemannian fibre norm).

All three are proved by the same compactness argument; see `Submission/Roadmap.lean` §126 for the
proof design, the gotchas, and how the parametric lift is assembled from them.

The proof of the first is the standard compactness argument: `closedBall 0 ρ'` is compact (finite
dimension), the injectivity of `GExp p` on it (from `InjAtLeast`) says that the pair-map
`(v,w) ↦ (GExp p v, GExp p w)` meets the diagonal only on the diagonal, and continuity turns this
into the ε-δ statement.  For the chart forms the same argument is run in the model space `E`, because
`M` carries no `FirstCountableTopology` instance in this context.
-/

namespace Submission.LiftUniform

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

/-- **Uniform continuity of the inverse of `GExp p` on a closed ball below the injectivity
radius.**  If `GExp p` is injective on the ball of radius `ρ` and `0 ≤ ρ' < ρ`, then for every
`ε > 0` there is `δ > 0` such that any two vectors of norm `≤ ρ'` whose images are at Riemannian
distance `< δ` differ by less than `ε`. -/
theorem exists_pos_forall_edist_lt_imp_norm_lt (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    {p : M} {ρ ρ' : ℝ} (hinj : InjAtLeast hmet p ρ) (hρ'0 : 0 ≤ ρ') (hρ'ρ : ρ' < ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v w : TangentSpace I p, ‖v‖ ≤ ρ' → ‖w‖ ≤ ρ' →
      Manifold.riemannianEDist I (GExp (cov := cov) hmet p v) (GExp (cov := cov) hmet p w)
        < ENNReal.ofReal δ →
      ‖v - w‖ < ε := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  haveI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  by_contra hcon
  push Not at hcon
  -- the failure: for each `n` there are `v n`, `w n` with close images but distant values
  have hbad : ∀ n : ℕ, ∃ v w : TangentSpace I p,
      ‖v‖ ≤ ρ' ∧ ‖w‖ ≤ ρ' ∧
        Manifold.riemannianEDist I (GExp (cov := cov) hmet p v) (GExp (cov := cov) hmet p w)
          < ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧ ε ≤ ‖v - w‖ :=
    fun n => hcon (1 / (n + 1 : ℝ)) (by positivity)
  choose v w hv using hbad
  have hv' : ∀ n, ‖v n‖ ≤ ρ' := fun n => (hv n).1
  have hw' : ∀ n, ‖w n‖ ≤ ρ' := fun n => (hv n).2.1
  have hcl : ∀ n, Manifold.riemannianEDist I (GExp (cov := cov) hmet p (v n))
      (GExp (cov := cov) hmet p (w n)) < ENNReal.ofReal (1 / (n + 1 : ℝ)) :=
    fun n => (hv n).2.2.1
  have hfar : ∀ n, ε ≤ ‖v n - w n‖ := fun n => (hv n).2.2.2
  -- compactness: extract a convergent subsequence of the pairs
  have hmemK : ∀ n, (v n, w n) ∈ Metric.closedBall (0 : TangentSpace I p) ρ'
      ×ˢ Metric.closedBall (0 : TangentSpace I p) ρ' := fun n =>
    ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hv' n,
     by rw [Metric.mem_closedBall, dist_zero_right]; exact hw' n⟩
  obtain ⟨z, hz, φ, hφ, hzlim⟩ := IsCompact.tendsto_subseq
    ((isCompact_closedBall (0 : TangentSpace I p) ρ').prod
      (isCompact_closedBall (0 : TangentSpace I p) ρ')) (x := fun n => (v n, w n)) hmemK
  set v₀ : TangentSpace I p := z.1 with hv₀
  set w₀ : TangentSpace I p := z.2 with hw₀
  have hzlim' : Tendsto (fun n => (v (φ n), w (φ n))) atTop (𝓝 (v₀, w₀)) := by
    have h := hzlim
    change Tendsto (fun n => (v (φ n), w (φ n))) atTop (𝓝 z) at h
    rwa [show z = (v₀, w₀) from by rw [hv₀, hw₀]] at h
  have hvs : Tendsto (fun n => v (φ n)) atTop (𝓝 v₀) :=
    (continuous_fst.tendsto ((v₀, w₀) : TangentSpace I p × TangentSpace I p)).comp hzlim'
  have hws : Tendsto (fun n => w (φ n)) atTop (𝓝 w₀) :=
    (continuous_snd.tendsto ((v₀, w₀) : TangentSpace I p × TangentSpace I p)).comp hzlim'
  have hv₀' : ‖v₀‖ ≤ ρ' := by
    rw [hv₀]
    have h := Metric.mem_closedBall.mp hz.1
    rwa [dist_zero_right] at h
  have hw₀' : ‖w₀‖ ≤ ρ' := by
    rw [hw₀]
    have h := Metric.mem_closedBall.mp hz.2
    rwa [dist_zero_right] at h
  -- the images converge
  have hcont := Submission.GExpRay2.continuousOn_GExp_closedBall_of_injAtLeast (cov := cov) hmet
    htor hinj ρ' (le_of_lt hρ'ρ)
  have hInK : ∀ n, v (φ n) ∈ Metric.closedBall (0 : TangentSpace I p) ρ' := fun n =>
    by rw [Metric.mem_closedBall, dist_zero_right]; exact hv' (φ n)
  have hInKw : ∀ n, w (φ n) ∈ Metric.closedBall (0 : TangentSpace I p) ρ' := fun n =>
    by rw [Metric.mem_closedBall, dist_zero_right]; exact hw' (φ n)
  have hbase : Tendsto (fun n => v (φ n)) atTop (𝓝[Metric.closedBall (0 : TangentSpace I p) ρ'] v₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hvs, Filter.Eventually.of_forall hInK⟩
  have hbasew : Tendsto (fun n => w (φ n)) atTop
      (𝓝[Metric.closedBall (0 : TangentSpace I p) ρ'] w₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hws, Filter.Eventually.of_forall hInKw⟩
  have hlimv : Tendsto (fun n => GExp (cov := cov) hmet p (v (φ n))) atTop
      (𝓝 (GExp (cov := cov) hmet p v₀)) :=
    (hcont.continuousWithinAt (Metric.mem_closedBall.mpr (by simpa using hv₀'))).tendsto.comp hbase
  have hlimw : Tendsto (fun n => GExp (cov := cov) hmet p (w (φ n))) atTop
      (𝓝 (GExp (cov := cov) hmet p w₀)) :=
    (hcont.continuousWithinAt (Metric.mem_closedBall.mpr (by simpa using hw₀'))).tendsto.comp hbasew
  -- the limit points are far apart, hence distinct
  have hlimnorm : Tendsto (fun n => ‖v (φ n) - w (φ n)‖) atTop (𝓝 ‖v₀ - w₀‖) :=
    ((hvs.sub hws).norm)
  have hfar₀ : ε ≤ ‖v₀ - w₀‖ :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlimnorm (fun n => hfar (φ n))
  have hne : v₀ ≠ w₀ := by
    intro h
    rw [h, sub_self, norm_zero] at hfar₀
    linarith
  -- and their images coincide, because the images of the pairs are close
  have himg : GExp (cov := cov) hmet p w₀ = GExp (cov := cov) hmet p v₀ := by
    refine tendsto_nhds_unique hlimw ?_
    refine tendsto_iff_forall_eventually_mem.mpr fun s hs => ?_
    obtain ⟨c, hc, hsub⟩ := Submission.EDist.setOf_riemannianEDist_lt_subset_nhds (I := I) hs
    have hc2 : (0 : ℝ≥0∞) < c / 2 := ENNReal.half_pos hc.ne'
    have h1 : ∀ᶠ n in atTop, Manifold.riemannianEDist I (GExp (cov := cov) hmet p v₀)
        (GExp (cov := cov) hmet p (v (φ n))) < c / 2 :=
      hlimv.eventually (Submission.EDist.eventually_riemannianEDist_lt (I := I)
        (GExp (cov := cov) hmet p v₀) hc2)
    have h2 : ∀ᶠ n in atTop, Manifold.riemannianEDist I (GExp (cov := cov) hmet p (v (φ n)))
        (GExp (cov := cov) hmet p (w (φ n))) < c / 2 := by
      have hsmall : ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal (1 / (n + 1 : ℝ)) < c / 2 := by
        have h : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop
            (𝓝 (ENNReal.ofReal (0 : ℝ))) :=
          (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        have hc2' : ENNReal.ofReal (0 : ℝ) < c / 2 := by simpa using hc2
        exact h.eventually_lt_const hc2'
      filter_upwards [hφ.tendsto_atTop.eventually hsmall] with n hn
      exact lt_of_lt_of_le (hcl (φ n)) hn.le
    filter_upwards [h1, h2] with n hn1 hn2
    refine hsub ?_
    calc Manifold.riemannianEDist I (GExp (cov := cov) hmet p v₀)
          (GExp (cov := cov) hmet p (w (φ n)))
        ≤ Manifold.riemannianEDist I (GExp (cov := cov) hmet p v₀)
            (GExp (cov := cov) hmet p (v (φ n)))
          + Manifold.riemannianEDist I (GExp (cov := cov) hmet p (v (φ n)))
            (GExp (cov := cov) hmet p (w (φ n))) := Manifold.riemannianEDist_triangle
      _ < c / 2 + c / 2 := ENNReal.add_lt_add hn1 hn2
      _ = c := ENNReal.add_halves c
  -- injectivity gives `v₀ = w₀`, contradiction
  have hltρ : ‖v₀‖ < ρ := lt_of_le_of_lt hv₀' hρ'ρ
  have hltρ' : ‖w₀‖ < ρ := lt_of_le_of_lt hw₀' hρ'ρ
  exact hne (hinj v₀ w₀ hltρ hltρ' (by rw [himg]))

/-- **Uniformity in the base point: the coordinate form of the inverse-continuity of `GExp`.**

Let `z₀` be a chart with flow data `D`, `Z` a compact set inside its source, and `η` a coordinate
radius satisfying the flow condition.  Suppose that `GExp q` is injective on the ball of radius `ρ`
for every `q ∈ Z`, and that every coordinate vector of norm `≤ η` at a point of `Z` has fibre norm
`< ρ`.  Then, **uniformly over `q ∈ Z`**, close images force close coordinates.

The pointwise version at a single base point is
`Submission.XuMain.exists_pos_edist_lt_imp_norm_sub_lt`, and the (non-uniform) ball version at a
single base point is `exists_pos_forall_edist_lt_imp_norm_lt` above.  This is the form needed by the
*parametric* (family) lifting argument, where the base point of the lift moves. -/
theorem exists_pos_forall_frameVector_edist_lt_imp_norm_sub_lt
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {z₀ : M} {Z : Set M} (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    (hZsrc : Z ⊆ (chartAt H z₀).source) (hZc : IsCompact Z)
    {η ρ : ℝ} (hηc : η ≤ 1 / (2 * flowScale D))
    (hinj : ∀ q ∈ Z, InjAtLeast hmet q ρ)
    (hnorm : ∀ q ∈ Z, ∀ u ∈ Metric.closedBall (0 : E) η,
      ‖Submission.Geodesic.frameVector (I := I) z₀ q u‖ < ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ Z, ∀ u ∈ Metric.closedBall (0 : E) η,
      ∀ u' ∈ Metric.closedBall (0 : E) η,
      Manifold.riemannianEDist I
        (GExp (cov := cov) hmet q (Submission.Geodesic.frameVector (I := I) z₀ q u))
        (GExp (cov := cov) hmet q (Submission.Geodesic.frameVector (I := I) z₀ q u'))
          < ENNReal.ofReal δ →
      ‖u - u'‖ < ε := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hcont := Submission.GExpJoint.contMDiffOn_GExp_frameVector (cov := cov) hmet D hZsrc hηc
  have hsub : Z ⊆ (extChartAt I z₀).source := fun q hq => by simpa using hZsrc hq
  have hsubT : ∀ q ∈ Z, (extChartAt I z₀) q ∈ (extChartAt I z₀).target :=
    fun q hq => PartialEquiv.map_source _ (hsub hq)
  have hsymm : ContinuousOn (fun x : E => (extChartAt I z₀).symm x) (extChartAt I z₀).target :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) z₀).continuousOn
  by_contra hcon
  push Not at hcon
  have hbad : ∀ n : ℕ, ∃ q ∈ Z, ∃ u ∈ Metric.closedBall (0 : E) η,
      ∃ u' ∈ Metric.closedBall (0 : E) η,
        Manifold.riemannianEDist I
          (GExp (cov := cov) hmet q (Submission.Geodesic.frameVector (I := I) z₀ q u))
          (GExp (cov := cov) hmet q (Submission.Geodesic.frameVector (I := I) z₀ q u'))
            < ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧ ε ≤ ‖u - u'‖ :=
    fun n => hcon (1 / (n + 1 : ℝ)) (by positivity)
  choose q hqZ u huB u' hu'B hspec using hbad
  -- compactness, performed in the chart coordinates `E × E × E`
  have hmemK : ∀ n, ((extChartAt I z₀) (q n), u n, u' n) ∈
      ((extChartAt I z₀) '' Z) ×ˢ
        (Metric.closedBall (0 : E) η ×ˢ Metric.closedBall (0 : E) η) :=
    fun n => ⟨⟨q n, hqZ n, rfl⟩, huB n, hu'B n⟩
  obtain ⟨z, hz, φ, hφ, hzlim⟩ := IsCompact.tendsto_subseq
    ((hZc.image_of_continuousOn ((continuousOn_extChartAt (I := I) z₀).mono hsub)).prod
      ((isCompact_closedBall (0 : E) η).prod (isCompact_closedBall (0 : E) η)))
    (x := fun n => ((extChartAt I z₀) (q n), u n, u' n)) hmemK
  obtain ⟨hzZ, hzu, hzu'⟩ := hz
  obtain ⟨q₀, hq₀Z, hq₀eq⟩ := hzZ
  have hq₀src : q₀ ∈ (extChartAt I z₀).source := hsub hq₀Z
  have hzlim' : Tendsto (fun n => ((extChartAt I z₀) (q (φ n)), u (φ n), u' (φ n))) atTop
      (𝓝 z) := hzlim
  have hxc : Tendsto (fun n => (extChartAt I z₀) (q (φ n))) atTop (𝓝 z.1) :=
    (continuous_fst.tendsto z).comp hzlim'
  have huc : Tendsto (fun n => u (φ n)) atTop (𝓝 z.2.1) :=
    (continuous_fst.tendsto z.2).comp ((continuous_snd.tendsto z).comp hzlim')
  have hu'c : Tendsto (fun n => u' (φ n)) atTop (𝓝 z.2.2) :=
    (continuous_snd.tendsto z.2).comp ((continuous_snd.tendsto z).comp hzlim')
  -- the base points converge in `M`
  have hsym : (extChartAt I z₀).symm z.1 = q₀ := by
    rw [← hq₀eq]
    exact PartialEquiv.left_inv (extChartAt I z₀) hq₀src
  have hqc : Tendsto (fun n => q (φ n)) atTop (𝓝 q₀) := by
    have hxc' : Tendsto (fun n => (extChartAt I z₀) (q (φ n))) atTop
        (𝓝 ((extChartAt I z₀) q₀)) := by
      rw [hq₀eq]; exact hxc
    have htend : Tendsto (fun n => (extChartAt I z₀) (q (φ n))) atTop
        (𝓝[(extChartAt I z₀).target] ((extChartAt I z₀) q₀)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hxc', Filter.Eventually.of_forall fun n => hsubT (q (φ n)) (hqZ (φ n))⟩
    have h1 : Tendsto (fun n => (extChartAt I z₀).symm ((extChartAt I z₀) (q (φ n)))) atTop
        (𝓝 ((extChartAt I z₀).symm ((extChartAt I z₀) q₀))) :=
      (hsymm.continuousWithinAt (hsubT q₀ hq₀Z)).tendsto.comp htend
    have h1' : Tendsto (fun n => (extChartAt I z₀).symm ((extChartAt I z₀) (q (φ n)))) atTop
        (𝓝 q₀) := by
      rwa [PartialEquiv.left_inv (extChartAt I z₀) hq₀src] at h1
    exact Tendsto.congr'
      (Filter.Eventually.of_forall fun n =>
        PartialEquiv.left_inv (extChartAt I z₀) (hsub (hqZ (φ n)))) h1'
  -- the two image sequences
  have hsq : ∀ n, (q (φ n), u (φ n)) ∈ Z ×ˢ Metric.closedBall (0 : E) η :=
    fun n => ⟨hqZ (φ n), huB (φ n)⟩
  have hsq' : ∀ n, (q (φ n), u' (φ n)) ∈ Z ×ˢ Metric.closedBall (0 : E) η :=
    fun n => ⟨hqZ (φ n), hu'B (φ n)⟩
  have hlim1 : Tendsto (fun n => GExp (cov := cov) hmet (q (φ n))
        (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u (φ n)))) atTop
      (𝓝 (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1))) := by
    have htend : Tendsto (fun n => (q (φ n), u (φ n))) atTop
        (𝓝[Z ×ˢ Metric.closedBall (0 : E) η] (q₀, z.2.1)) :=
      tendsto_nhdsWithin_iff.mpr ⟨(Prod.tendsto_iff (fun n => (q (φ n), u (φ n))) (q₀, z.2.1)).mpr ⟨hqc, huc⟩, Filter.Eventually.of_forall hsq⟩
    exact ((hcont.continuousOn).continuousWithinAt ⟨hq₀Z, hzu⟩).tendsto.comp htend
  have hlim2 : Tendsto (fun n => GExp (cov := cov) hmet (q (φ n))
        (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u' (φ n)))) atTop
      (𝓝 (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.2))) := by
    have htend : Tendsto (fun n => (q (φ n), u' (φ n))) atTop
        (𝓝[Z ×ˢ Metric.closedBall (0 : E) η] (q₀, z.2.2)) :=
      tendsto_nhdsWithin_iff.mpr ⟨(Prod.tendsto_iff (fun n => (q (φ n), u' (φ n))) (q₀, z.2.2)).mpr ⟨hqc, hu'c⟩, Filter.Eventually.of_forall hsq'⟩
    exact ((hcont.continuousOn).continuousWithinAt ⟨hq₀Z, hzu'⟩).tendsto.comp htend
  -- the second sequence also tends to the first limit
  have hmix : Tendsto (fun n => GExp (cov := cov) hmet (q (φ n))
        (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u' (φ n)))) atTop
      (𝓝 (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1))) := by
    refine tendsto_iff_forall_eventually_mem.mpr fun s hs => ?_
    obtain ⟨c, hc, hsub'⟩ := Submission.EDist.setOf_riemannianEDist_lt_subset_nhds (I := I) hs
    have hc2 : (0 : ℝ≥0∞) < c / 2 := ENNReal.half_pos hc.ne'
    have h1 : ∀ᶠ n in atTop, Manifold.riemannianEDist I
        (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1))
        (GExp (cov := cov) hmet (q (φ n))
          (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u (φ n)))) < c / 2 :=
      hlim1.eventually (Submission.EDist.eventually_riemannianEDist_lt (I := I)
        (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1)) hc2)
    have hsmall : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (1 / (n + 1 : ℝ)) < c / 2 := by
      have h : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop
          (𝓝 (ENNReal.ofReal (0 : ℝ))) :=
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hc2' : ENNReal.ofReal (0 : ℝ) < c / 2 := by simpa using hc2
      exact h.eventually_lt_const hc2'
    have h2 : ∀ᶠ n in atTop, Manifold.riemannianEDist I
        (GExp (cov := cov) hmet (q (φ n))
          (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u (φ n))))
        (GExp (cov := cov) hmet (q (φ n))
          (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u' (φ n)))) < c / 2 := by
      filter_upwards [hφ.tendsto_atTop.eventually hsmall] with n hn
      exact lt_of_lt_of_le (hspec (φ n)).1 hn.le
    filter_upwards [h1, h2] with n hn1 hn2
    refine hsub' ?_
    calc Manifold.riemannianEDist I
          (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1))
          (GExp (cov := cov) hmet (q (φ n))
            (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u' (φ n))))
        ≤ Manifold.riemannianEDist I
            (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1))
            (GExp (cov := cov) hmet (q (φ n))
              (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u (φ n))))
          + Manifold.riemannianEDist I
            (GExp (cov := cov) hmet (q (φ n))
              (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u (φ n))))
            (GExp (cov := cov) hmet (q (φ n))
              (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u' (φ n)))) :=
          Manifold.riemannianEDist_triangle
      _ < c / 2 + c / 2 := ENNReal.add_lt_add hn1 hn2
      _ = c := ENNReal.add_halves c
  -- injectivity at the limit gives `z.2.2 = z.2.1`, contradicting the separation
  have himg : GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.2)
      = GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1) :=
    tendsto_nhds_unique hlim2 hmix
  have hfv : Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.2
      = Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1 :=
    hinj q₀ hq₀Z _ _ (hnorm q₀ hq₀Z z.2.2 hzu') (hnorm q₀ hq₀Z z.2.1 hzu) (by rw [himg])
  have hsubv : Submission.Geodesic.frameVector (I := I) z₀ q₀ (z.2.2 - z.2.1) = 0 := by
    have h1 : Submission.Geodesic.frameVector (I := I) z₀ q₀ (z.2.2 - z.2.1)
        = Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.2
          - Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1 := by
      rw [sub_eq_add_neg, ← neg_one_smul ℝ z.2.1, Submission.Geodesic.frameVector_add,
        Submission.Geodesic.frameVector_smul, neg_one_smul, sub_eq_add_neg]
    rw [h1, hfv, sub_self]
  have hzero : z.2.2 - z.2.1 = 0 :=
    (Submission.ChartBounds.frameVector_eq_zero_iff (I := I) (x₀ := z₀) (p := q₀)
      (by simpa using hq₀src) (z.2.2 - z.2.1)).mp hsubv
  have hfarlim : ε ≤ ‖z.2.1 - z.2.2‖ :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds ((huc.sub hu'c).norm)
      (fun n => (hspec (φ n)).2)
  rw [← (sub_eq_zero.mp hzero), sub_self, norm_zero] at hfarlim
  linarith

/-- **The joint (moving base point) form of the inverse-continuity of `GExp`.**

Same setting as `exists_pos_forall_frameVector_edist_lt_imp_norm_sub_lt`, but the two points may have
*different* base points in the same chart piece: if the chart coordinates of the base points are close
**and** the images under the exponential map are close, then the coordinate vectors are close.

This is the form the *parametric* lifting argument consumes: the base points of the lifts of a family
of curves move, and the trivialisation by the chart makes the moving tangent spaces comparable. -/
theorem exists_pos_joint_frameVector_edist_lt_imp_norm_sub_lt
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {z₀ : M} {Z : Set M} (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    (hZsrc : Z ⊆ (chartAt H z₀).source) (hZc : IsCompact Z)
    {η ρ : ℝ} (hηc : η ≤ 1 / (2 * flowScale D))
    (hinj : ∀ q ∈ Z, InjAtLeast hmet q ρ)
    (hnorm : ∀ q ∈ Z, ∀ u ∈ Metric.closedBall (0 : E) η,
      ‖Submission.Geodesic.frameVector (I := I) z₀ q u‖ < ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ Z, ∀ q' ∈ Z,
      ∀ u ∈ Metric.closedBall (0 : E) η, ∀ u' ∈ Metric.closedBall (0 : E) η,
      ‖(extChartAt I z₀) q - (extChartAt I z₀) q'‖ < δ →
      Manifold.riemannianEDist I
        (GExp (cov := cov) hmet q (Submission.Geodesic.frameVector (I := I) z₀ q u))
        (GExp (cov := cov) hmet q' (Submission.Geodesic.frameVector (I := I) z₀ q' u'))
          < ENNReal.ofReal δ →
      ‖u - u'‖ < ε := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hcont := Submission.GExpJoint.contMDiffOn_GExp_frameVector (cov := cov) hmet D hZsrc hηc
  have hsub : Z ⊆ (extChartAt I z₀).source := fun q hq => by simpa using hZsrc hq
  have hsubT : ∀ q ∈ Z, (extChartAt I z₀) q ∈ (extChartAt I z₀).target :=
    fun q hq => PartialEquiv.map_source _ (hsub hq)
  have hsymm : ContinuousOn (fun x : E => (extChartAt I z₀).symm x) (extChartAt I z₀).target :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) z₀).continuousOn
  by_contra hcon
  push Not at hcon
  have hbad : ∀ n : ℕ, ∃ q ∈ Z, ∃ q' ∈ Z, ∃ u ∈ Metric.closedBall (0 : E) η,
      ∃ u' ∈ Metric.closedBall (0 : E) η,
        ‖(extChartAt I z₀) q - (extChartAt I z₀) q'‖ < 1 / (n + 1 : ℝ) ∧
        Manifold.riemannianEDist I
          (GExp (cov := cov) hmet q (Submission.Geodesic.frameVector (I := I) z₀ q u))
          (GExp (cov := cov) hmet q' (Submission.Geodesic.frameVector (I := I) z₀ q' u'))
            < ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧ ε ≤ ‖u - u'‖ :=
    fun n => hcon (1 / (n + 1 : ℝ)) (by positivity)
  choose q hqZ q' hq'Z u huB u' hu'B hspec using hbad
  have hmemK : ∀ n, (((extChartAt I z₀) (q n), (extChartAt I z₀) (q' n)), (u n, u' n)) ∈
      (((extChartAt I z₀) '' Z) ×ˢ ((extChartAt I z₀) '' Z)) ×ˢ
        (Metric.closedBall (0 : E) η ×ˢ Metric.closedBall (0 : E) η) :=
    fun n => ⟨⟨⟨q n, hqZ n, rfl⟩, ⟨q' n, hq'Z n, rfl⟩⟩, huB n, hu'B n⟩
  obtain ⟨z, hz, φ, hφ, hzlim⟩ := IsCompact.tendsto_subseq
    (((hZc.image_of_continuousOn ((continuousOn_extChartAt (I := I) z₀).mono hsub)).prod
        (hZc.image_of_continuousOn ((continuousOn_extChartAt (I := I) z₀).mono hsub))).prod
      ((isCompact_closedBall (0 : E) η).prod (isCompact_closedBall (0 : E) η)))
    (x := fun n => (((extChartAt I z₀) (q n), (extChartAt I z₀) (q' n)), (u n, u' n))) hmemK
  obtain ⟨⟨hzZ, hzZ'⟩, hzu, hzu'⟩ := hz
  obtain ⟨q₀, hq₀Z, hq₀eq⟩ := hzZ
  obtain ⟨q₁, hq₁Z, hq₁eq⟩ := hzZ'
  have hq₀src : q₀ ∈ (extChartAt I z₀).source := hsub hq₀Z
  have hq₁src : q₁ ∈ (extChartAt I z₀).source := hsub hq₁Z
  have hzlim' : Tendsto (fun n => (((extChartAt I z₀) (q (φ n)), (extChartAt I z₀) (q' (φ n))),
      (u (φ n), u' (φ n)))) atTop (𝓝 z) := hzlim
  have hxc : Tendsto (fun n => (extChartAt I z₀) (q (φ n))) atTop (𝓝 z.1.1) :=
    (continuous_fst.tendsto z.1).comp ((continuous_fst.tendsto z).comp hzlim')
  have hxc' : Tendsto (fun n => (extChartAt I z₀) (q' (φ n))) atTop (𝓝 z.1.2) :=
    (continuous_snd.tendsto z.1).comp ((continuous_fst.tendsto z).comp hzlim')
  have huc : Tendsto (fun n => u (φ n)) atTop (𝓝 z.2.1) :=
    (continuous_fst.tendsto z.2).comp ((continuous_snd.tendsto z).comp hzlim')
  have hu'c : Tendsto (fun n => u' (φ n)) atTop (𝓝 z.2.2) :=
    (continuous_snd.tendsto z.2).comp ((continuous_snd.tendsto z).comp hzlim')
  -- the chart coordinates of the base points coincide in the limit, hence so do the base points
  have hdchart : Tendsto (fun n => ‖(extChartAt I z₀) (q (φ n)) - (extChartAt I z₀) (q' (φ n))‖)
      atTop (𝓝 ‖z.1.1 - z.1.2‖) := (hxc.sub hxc').norm
  have hchartlim : z.1.1 = z.1.2 := by
    have hsmall : Tendsto (fun n : ℕ => 1 / (φ n + 1 : ℝ)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
    have h0 : ‖z.1.1 - z.1.2‖ ≤ 0 := by
      refine le_of_tendsto_of_tendsto' hdchart hsmall ?_
      intro n
      exact le_of_lt ((hspec (φ n)).1)
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h0 (norm_nonneg _)))
  have hqq' : q₀ = q₁ := by
    have heq : (extChartAt I z₀) q₀ = (extChartAt I z₀) q₁ := by
      rw [hq₀eq, hq₁eq]
      exact hchartlim
    have hs : (extChartAt I z₀).symm ((extChartAt I z₀) q₀)
        = (extChartAt I z₀).symm ((extChartAt I z₀) q₁) := by rw [heq]
    rwa [PartialEquiv.left_inv (extChartAt I z₀) hq₀src,
      PartialEquiv.left_inv (extChartAt I z₀) hq₁src] at hs
  subst hqq'
  -- the base points converge in `M`
  have hqc : Tendsto (fun n => q (φ n)) atTop (𝓝 q₀) := by
    have hxc'' : Tendsto (fun n => (extChartAt I z₀) (q (φ n))) atTop
        (𝓝 ((extChartAt I z₀) q₀)) := by
      rw [hq₀eq]; exact hxc
    have htend : Tendsto (fun n => (extChartAt I z₀) (q (φ n))) atTop
        (𝓝[(extChartAt I z₀).target] ((extChartAt I z₀) q₀)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hxc'', Filter.Eventually.of_forall fun n => hsubT (q (φ n)) (hqZ (φ n))⟩
    have h1 : Tendsto (fun n => (extChartAt I z₀).symm ((extChartAt I z₀) (q (φ n)))) atTop
        (𝓝 ((extChartAt I z₀).symm ((extChartAt I z₀) q₀))) :=
      (hsymm.continuousWithinAt (hsubT q₀ hq₀Z)).tendsto.comp htend
    have h1' : Tendsto (fun n => (extChartAt I z₀).symm ((extChartAt I z₀) (q (φ n)))) atTop
        (𝓝 q₀) := by
      rwa [PartialEquiv.left_inv (extChartAt I z₀) hq₀src] at h1
    exact Tendsto.congr'
      (Filter.Eventually.of_forall fun n =>
        PartialEquiv.left_inv (extChartAt I z₀) (hsub (hqZ (φ n)))) h1'
  have hq'c : Tendsto (fun n => q' (φ n)) atTop (𝓝 q₀) := by
    have hxc'' : Tendsto (fun n => (extChartAt I z₀) (q' (φ n))) atTop
        (𝓝 ((extChartAt I z₀) q₀)) := by
      rw [hq₁eq]; exact hxc'
    have htend : Tendsto (fun n => (extChartAt I z₀) (q' (φ n))) atTop
        (𝓝[(extChartAt I z₀).target] ((extChartAt I z₀) q₀)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hxc'', Filter.Eventually.of_forall fun n => hsubT (q' (φ n)) (hq'Z (φ n))⟩
    have h1 : Tendsto (fun n => (extChartAt I z₀).symm ((extChartAt I z₀) (q' (φ n)))) atTop
        (𝓝 ((extChartAt I z₀).symm ((extChartAt I z₀) q₀))) :=
      (hsymm.continuousWithinAt (hsubT q₀ hq₀Z)).tendsto.comp htend
    have h1' : Tendsto (fun n => (extChartAt I z₀).symm ((extChartAt I z₀) (q' (φ n)))) atTop
        (𝓝 q₀) := by
      rwa [PartialEquiv.left_inv (extChartAt I z₀) hq₀src] at h1
    exact Tendsto.congr'
      (Filter.Eventually.of_forall fun n =>
        PartialEquiv.left_inv (extChartAt I z₀) (hsub (hq'Z (φ n)))) h1'
  -- the two image sequences
  have hsq : ∀ n, (q (φ n), u (φ n)) ∈ Z ×ˢ Metric.closedBall (0 : E) η :=
    fun n => ⟨hqZ (φ n), huB (φ n)⟩
  have hsq' : ∀ n, (q' (φ n), u' (φ n)) ∈ Z ×ˢ Metric.closedBall (0 : E) η :=
    fun n => ⟨hq'Z (φ n), hu'B (φ n)⟩
  have hlim1 : Tendsto (fun n => GExp (cov := cov) hmet (q (φ n))
        (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u (φ n)))) atTop
      (𝓝 (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1))) := by
    have htend : Tendsto (fun n => (q (φ n), u (φ n))) atTop
        (𝓝[Z ×ˢ Metric.closedBall (0 : E) η] (q₀, z.2.1)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨(Prod.tendsto_iff (fun n => (q (φ n), u (φ n))) (q₀, z.2.1)).mpr ⟨hqc, huc⟩,
          Filter.Eventually.of_forall hsq⟩
    exact ((hcont.continuousOn).continuousWithinAt ⟨hq₀Z, hzu⟩).tendsto.comp htend
  have hlim2 : Tendsto (fun n => GExp (cov := cov) hmet (q' (φ n))
        (Submission.Geodesic.frameVector (I := I) z₀ (q' (φ n)) (u' (φ n)))) atTop
      (𝓝 (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.2))) := by
    have htend : Tendsto (fun n => (q' (φ n), u' (φ n))) atTop
        (𝓝[Z ×ˢ Metric.closedBall (0 : E) η] (q₀, z.2.2)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨(Prod.tendsto_iff (fun n => (q' (φ n), u' (φ n))) (q₀, z.2.2)).mpr ⟨hq'c, hu'c⟩,
          Filter.Eventually.of_forall hsq'⟩
    exact ((hcont.continuousOn).continuousWithinAt ⟨hq₀Z, hzu'⟩).tendsto.comp htend
  -- the second sequence also tends to the first limit
  have hmix : Tendsto (fun n => GExp (cov := cov) hmet (q' (φ n))
        (Submission.Geodesic.frameVector (I := I) z₀ (q' (φ n)) (u' (φ n)))) atTop
      (𝓝 (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1))) := by
    refine tendsto_iff_forall_eventually_mem.mpr fun s hs => ?_
    obtain ⟨c, hc, hsub'⟩ := Submission.EDist.setOf_riemannianEDist_lt_subset_nhds (I := I) hs
    have hc2 : (0 : ℝ≥0∞) < c / 2 := ENNReal.half_pos hc.ne'
    have h1 : ∀ᶠ n in atTop, Manifold.riemannianEDist I
        (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1))
        (GExp (cov := cov) hmet (q (φ n))
          (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u (φ n)))) < c / 2 :=
      hlim1.eventually (Submission.EDist.eventually_riemannianEDist_lt (I := I)
        (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1)) hc2)
    have hsmall : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (1 / (n + 1 : ℝ)) < c / 2 := by
      have h : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop
          (𝓝 (ENNReal.ofReal (0 : ℝ))) :=
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hc2' : ENNReal.ofReal (0 : ℝ) < c / 2 := by simpa using hc2
      exact h.eventually_lt_const hc2'
    have h2 : ∀ᶠ n in atTop, Manifold.riemannianEDist I
        (GExp (cov := cov) hmet (q (φ n))
          (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u (φ n))))
        (GExp (cov := cov) hmet (q' (φ n))
          (Submission.Geodesic.frameVector (I := I) z₀ (q' (φ n)) (u' (φ n)))) < c / 2 := by
      filter_upwards [hφ.tendsto_atTop.eventually hsmall] with n hn
      exact lt_of_lt_of_le (hspec (φ n)).2.1 hn.le
    filter_upwards [h1, h2] with n hn1 hn2
    refine hsub' ?_
    calc Manifold.riemannianEDist I
          (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1))
          (GExp (cov := cov) hmet (q' (φ n))
            (Submission.Geodesic.frameVector (I := I) z₀ (q' (φ n)) (u' (φ n))))
        ≤ Manifold.riemannianEDist I
            (GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1))
            (GExp (cov := cov) hmet (q (φ n))
              (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u (φ n))))
          + Manifold.riemannianEDist I
            (GExp (cov := cov) hmet (q (φ n))
              (Submission.Geodesic.frameVector (I := I) z₀ (q (φ n)) (u (φ n))))
            (GExp (cov := cov) hmet (q' (φ n))
              (Submission.Geodesic.frameVector (I := I) z₀ (q' (φ n)) (u' (φ n)))) :=
          Manifold.riemannianEDist_triangle
      _ < c / 2 + c / 2 := ENNReal.add_lt_add hn1 hn2
      _ = c := ENNReal.add_halves c
  -- injectivity at the limit gives `z.2.2 = z.2.1`, contradicting the separation
  have himg : GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.2)
      = GExp (cov := cov) hmet q₀ (Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1) :=
    tendsto_nhds_unique hlim2 hmix
  have hfv : Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.2
      = Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1 :=
    hinj q₀ hq₀Z _ _ (hnorm q₀ hq₀Z z.2.2 hzu') (hnorm q₀ hq₀Z z.2.1 hzu) (by rw [himg])
  have hsubv : Submission.Geodesic.frameVector (I := I) z₀ q₀ (z.2.2 - z.2.1) = 0 := by
    have h1 : Submission.Geodesic.frameVector (I := I) z₀ q₀ (z.2.2 - z.2.1)
        = Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.2
          - Submission.Geodesic.frameVector (I := I) z₀ q₀ z.2.1 := by
      rw [sub_eq_add_neg, ← neg_one_smul ℝ z.2.1, Submission.Geodesic.frameVector_add,
        Submission.Geodesic.frameVector_smul, neg_one_smul, sub_eq_add_neg]
    rw [h1, hfv, sub_self]
  have hzero : z.2.2 - z.2.1 = 0 :=
    (Submission.ChartBounds.frameVector_eq_zero_iff (I := I) (x₀ := z₀) (p := q₀)
      (by simpa using hq₀src) (z.2.2 - z.2.1)).mp hsubv
  have hfarlim : ε ≤ ‖z.2.1 - z.2.2‖ :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds ((huc.sub hu'c).norm)
      (fun n => (hspec (φ n)).2.2)
  rw [← (sub_eq_zero.mp hzero), sub_self, norm_zero] at hfarlim
  linarith

/-- **The fibre-norm form, uniform over a compact chart piece.**

The counterpart of `exists_pos_forall_edist_lt_imp_norm_lt` (fixed base point, fibre norm) in which
the base point is allowed to vary over a compact set `Z` inside one chart.  The existential radius
`ρ'` is a little smaller than the injectivity radius `ρ` because the chart trivialisation is only
comparable to the fibre norm through the chart Gram bounds; for the applications (lifting arguments)
only the positivity and the uniformity matter.

Proof: the chart Gram bounds give `√λ ‖u‖ ≤ ‖v‖ ≤ √Λ ‖u‖` for the coordinate vector `u = clm q v`;
the coordinate version `exists_pos_forall_frameVector_edist_lt_imp_norm_sub_lt` applies on the
coordinate ball of radius `η ≤ min (1/(2 flowScale D)) (ρ/(2√Λ))`, and the two Gram comparisons
convert its conclusion into the fibre norm. -/
theorem exists_pos_forall_edist_lt_imp_norm_sub_lt_of_chart (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    {z₀ : M} {Z : Set M} (hZsrc : Z ⊆ (chartAt H z₀).source) (hZc : IsCompact Z)
    (hZne : Z.Nonempty) {ρ : ℝ} (hρ : 0 < ρ) (hinj : ∀ q ∈ Z, InjAtLeast hmet q ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ q ∈ Z, ∀ v w : TangentSpace I q, ‖v‖ ≤ ρ' → ‖w‖ ≤ ρ' →
        Manifold.riemannianEDist I (GExp (cov := cov) hmet q v)
          (GExp (cov := cov) hmet q w) < ENNReal.ofReal δ → ‖v - w‖ < ε := by
  classical
  have hsub : Z ⊆ (extChartAt I z₀).source := fun q hq => by simpa using hZsrc hq
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ :=
    Submission.ChartBounds.exists_chartGram_bounds (I := I) z₀ hZc hZne hZsrc
  have hsqlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsqLam : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hLam
  obtain ⟨D, -⟩ := Submission.GExpFlow.exists_chartFlowData (cov := cov) (I := I)
    (z₀ := z₀) (Z := Z) hZc hZsrc
  have hfs : 0 < flowScale D := Submission.GExpFlow.flowScale_pos D
  set η : ℝ := min (1 / (2 * flowScale D)) (ρ / (2 * Real.sqrt Lam)) with hηdef
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  have hηc : η ≤ 1 / (2 * flowScale D) := min_le_left _ _
  have hηΛ : Real.sqrt Lam * η ≤ ρ / 2 := by
    have h : η ≤ ρ / (2 * Real.sqrt Lam) := min_le_right _ _
    have h2 : Real.sqrt Lam * (ρ / (2 * Real.sqrt Lam)) = ρ / 2 := by
      field_simp
    calc Real.sqrt Lam * η ≤ Real.sqrt Lam * (ρ / (2 * Real.sqrt Lam)) := by
          exact mul_le_mul_of_nonneg_left h hsqLam.le
      _ = ρ / 2 := h2
  have hnorm : ∀ q ∈ Z, ∀ u ∈ Metric.closedBall (0 : E) η,
      ‖Submission.Geodesic.frameVector (I := I) z₀ q u‖ < ρ := by
    intro q hq u hu
    have hu' : ‖u‖ ≤ η := by simpa [Metric.mem_closedBall, dist_eq_norm] using hu
    have h1 : ‖Submission.Geodesic.frameVector (I := I) z₀ q u‖
        = Real.sqrt (chartGram (I := I) z₀ q u u) := Submission.GExpFlow.norm_frameVector (I := I) u
    rw [h1]
    have hchain : Real.sqrt (chartGram (I := I) z₀ q u u) ≤ Real.sqrt Lam * η := by
      calc Real.sqrt (chartGram (I := I) z₀ q u u) ≤ Real.sqrt (Lam * ‖u‖ ^ 2) :=
            Real.sqrt_le_sqrt (hbnd q hq u).2
        _ = Real.sqrt Lam * ‖u‖ := by
            rw [Real.sqrt_mul hLam.le, Real.sqrt_sq (norm_nonneg u)]
        _ ≤ Real.sqrt Lam * η := mul_le_mul_of_nonneg_left hu' hsqLam.le
    have hlt : Real.sqrt Lam * η < ρ := by linarith
    linarith
  obtain ⟨δ, hδpos, hδspec⟩ :=
    exists_pos_forall_frameVector_edist_lt_imp_norm_sub_lt (cov := cov) hmet htor D hZsrc hZc
      hηc hinj hnorm (show 0 < ε / Real.sqrt Lam by positivity)
  refine ⟨min ρ (η * Real.sqrt lam), ?_, ?_, δ, hδpos, ?_⟩
  · exact lt_min hρ (by positivity)
  · exact min_le_left _ _
  · intro q hq v w hv hw himg
    have hbnd1 : ‖v‖ ≤ Real.sqrt lam * η := by
      rw [mul_comm]; exact le_trans hv (min_le_right _ _)
    have hbnd1' : ‖w‖ ≤ Real.sqrt lam * η := by
      rw [mul_comm]; exact le_trans hw (min_le_right _ _)
    set u : E := (trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q v with hudef
    set u' : E := (trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q w with hu'def
    have hvu : Submission.Geodesic.frameVector (I := I) z₀ q u = v :=
      Submission.GExpFlow.frameVector_clm (I := I) (hsub hq) v
    have hwu : Submission.Geodesic.frameVector (I := I) z₀ q u' = w :=
      Submission.GExpFlow.frameVector_clm (I := I) (hsub hq) w
    have hulat : Real.sqrt lam * ‖u‖ ≤ ‖v‖ := by
      have h := (hbnd q hq u).1
      have h2 : Real.sqrt (lam * ‖u‖ ^ 2) ≤ Real.sqrt (chartGram (I := I) z₀ q u u) :=
        Real.sqrt_le_sqrt h
      rw [Real.sqrt_mul hlam.le, Real.sqrt_sq (norm_nonneg u)] at h2
      rw [← Submission.GExpFlow.norm_frameVector (I := I) u] at h2
      rw [hvu] at h2
      exact h2
    have hulatu' : Real.sqrt lam * ‖u'‖ ≤ ‖w‖ := by
      have h := (hbnd q hq u').1
      have h2 : Real.sqrt (lam * ‖u'‖ ^ 2) ≤ Real.sqrt (chartGram (I := I) z₀ q u' u') :=
        Real.sqrt_le_sqrt h
      rw [Real.sqrt_mul hlam.le, Real.sqrt_sq (norm_nonneg u')] at h2
      rw [← Submission.GExpFlow.norm_frameVector (I := I) u'] at h2
      rw [hwu] at h2
      exact h2
    have huB : u ∈ Metric.closedBall (0 : E) η := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_of_mul_le_mul_left (le_trans hulat hbnd1) hsqlam
    have hu'B : u' ∈ Metric.closedBall (0 : E) η := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_of_mul_le_mul_left (le_trans hulatu' hbnd1') hsqlam
    have hδ := hδspec q hq u huB u' hu'B (by rw [hvu, hwu]; exact himg)
    -- `‖v - w‖ ≤ √Λ ‖u - u'‖`
    have hnormdiff : ‖v - w‖ ≤ Real.sqrt Lam * ‖u - u'‖ := by
      have h1 : v - w = Submission.Geodesic.frameVector (I := I) z₀ q (u - u') := by
        rw [Submission.ChartCurv.frameVector_sub, hvu, hwu]
      rw [h1, Submission.GExpFlow.norm_frameVector]
      calc Real.sqrt (chartGram (I := I) z₀ q (u - u') (u - u'))
          ≤ Real.sqrt (Lam * ‖u - u'‖ ^ 2) := Real.sqrt_le_sqrt (hbnd q hq (u - u')).2
        _ = Real.sqrt Lam * ‖u - u'‖ := by
            rw [Real.sqrt_mul hLam.le, Real.sqrt_sq (norm_nonneg _)]
    have : ‖u - u'‖ < ε / Real.sqrt Lam := hδ
    have h2 := mul_lt_mul_of_pos_left this hsqLam
    rw [mul_div_cancel₀ _ (ne_of_gt hsqLam)] at h2
    exact lt_of_le_of_lt hnormdiff h2

end

end Submission.LiftUniform
