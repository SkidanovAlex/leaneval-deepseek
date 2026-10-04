import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.polygon.minimiser_unique_of_mem_segmentDomain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.polygon

set_option linter.style.haveILetI false

open scoped ContDiff Manifold ENNReal
open Bundle Filter
open scoped Topology


/-- **Every minimising vector from `q` to a point `y` close to `p = GExp q U` is close to `U`**, when
`U` lies in the tangential segment domain at `q` (i.e. the ray of `U` is *strictly* minimising at
`‖U‖`; equivalently `p` is not a cut point of `q`).

Here `V` is a *minimising* vector for `y`: `GExp q V = y` and `d(q,y) = ‖V‖`.

Suggested route (the classical "minimising geodesics converge" argument, cf. Roadmap §55.1).  The
differential-geometric input is `Submission.SegmentDomain.cutTime_le_of_meet`, and a minimising
vector for any point is produced by `Submission.HopfRinow2.exists_geodesic_riemannianEDist_eq`.
Suppose the conclusion fails: there are `yₙ` with `d(p,yₙ) < 1/(n+1)` and minimising `Vₙ` with
`‖Vₙ - U‖ ≥ r`.  Then

* `‖Vₙ‖ = d(q,yₙ) → ‖U‖` by the triangle inequality together with
  `d(q,p) = ‖U‖` (`Submission.SegmentDomain.edist_GExp_eq_norm_of_mem_segmentDomain`); so the `Vₙ`
  lie in a closed ball of `T_qM`, which is compact, and a subsequence converges to some `V_∞` with
  `‖V_∞‖ = ‖U‖` (`IsCompact.tendsto_subseq`);
* `GExp q` is continuous at `V_∞` (`Submission.GExpLocalInj.contMDiffAt_GExp_one`) and `z ↦ d(p,z)`
  is continuous (`Submission.HopfRinow.continuous_riemannianEDist_left`), so
  `d(p, GExp q V_∞) = 0`, i.e. `GExp q V_∞ = p`;
* uniqueness of the minimising vector from `q` to `p` (the sibling result
  `minimiser_unique_of_mem_segmentDomain` of this folder, or the same argument inline via
  `cutTime_le_of_meet`) gives `V_∞ = U`, contradicting `‖Vₙ - U‖ ≥ r`.

The prover may bring in the sibling `minimiser_unique_of_mem_segmentDomain` or repeat its short
argument.  The module `Submission.HopfRinow2` is likely also needed. -/
theorem minimisers_cluster_near_segmentDomain
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
    {r : ℝ} (hr : 0 < r) :
    ∃ ε > 0, ∀ (y : M), Manifold.riemannianEDist I p y < ENNReal.ofReal ε →
      ∀ V : TangentSpace I q, Submission.GlobalExp.GExp (cov := cov) hmet q V = y →
        Manifold.riemannianEDist I q y = ENNReal.ofReal ‖V‖ → ‖V - U‖ < r := by
  classical
  -- the ambient Riemannian bundle is continuous, so the Riemannian distance is well behaved
  haveI hcb : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  -- uniqueness of the minimising vector from `q` to `p`
  have huniq : ∀ V : TangentSpace I q,
      Submission.GlobalExp.GExp (cov := cov) hmet q V = p → ‖V‖ = ‖U‖ → V = U :=
    fun V hV hVn => minimiser_unique_of_mem_segmentDomain hmet htor hU hseg hUp hV hVn
  -- `p` is at distance `‖U‖` from `q`
  have hqU : Manifold.riemannianEDist I q p = ENNReal.ofReal ‖U‖ := by
    rw [← hUp]
    exact Submission.SegmentDomain.edist_GExp_eq_norm_of_mem_segmentDomain (cov := cov) hmet htor hseg
  by_contra hcon
  push Not at hcon
  -- a sequence of counterexamples: `y n → p` and minimising `V n` with `‖V n - U‖ ≥ r`
  have hseq : ∀ n : ℕ, ∃ (y : M) (V : TangentSpace I q),
      Manifold.riemannianEDist I p y < ENNReal.ofReal (((n : ℝ) + 1)⁻¹) ∧
      Submission.GlobalExp.GExp (cov := cov) hmet q V = y ∧
      Manifold.riemannianEDist I q y = ENNReal.ofReal ‖V‖ ∧ r ≤ ‖V - U‖ := by
    intro n
    obtain ⟨y, hy, V, h1, h2, h3⟩ := hcon (((n : ℝ) + 1)⁻¹) (by positivity)
    exact ⟨y, V, hy, h1, h2, h3⟩
  choose y V hy hVexp hVnorm hVfar using hseq
  -- `1 / (n+1) ≤ 1`
  have hle1 : ∀ n : ℕ, (((n : ℝ) + 1))⁻¹ ≤ 1 := by
    intro n
    have h : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    exact inv_le_one_of_one_le₀ h
  -- the norms of the `V n` are bounded
  have hVnorm_toReal : ∀ n : ℕ,
      ‖V n‖ = (Manifold.riemannianEDist I q (y n)).toReal := by
    intro n
    rw [hVnorm n, ENNReal.toReal_ofReal (norm_nonneg (V n))]
  have hbound : ∀ n : ℕ, ‖V n‖ ≤ ‖U‖ + 1 := by
    intro n
    have htri : Manifold.riemannianEDist I q (y n)
        ≤ Manifold.riemannianEDist I q p + Manifold.riemannianEDist I p (y n) :=
      Manifold.riemannianEDist_triangle (I := I) (x := q) (y := p) (z := y n)
    rw [hqU] at htri
    have h2 : Manifold.riemannianEDist I q (y n) ≤ ENNReal.ofReal (‖U‖ + 1) := by
      refine htri.trans ?_
      rw [ENNReal.ofReal_add (norm_nonneg U) (by norm_num : (0 : ℝ) ≤ 1)]
      exact add_le_add le_rfl (le_trans (hy n).le (ENNReal.ofReal_le_ofReal (hle1 n)))
    calc ‖V n‖ = (Manifold.riemannianEDist I q (y n)).toReal := hVnorm_toReal n
      _ ≤ (ENNReal.ofReal (‖U‖ + 1)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
      _ = ‖U‖ + 1 := ENNReal.toReal_ofReal (by positivity)
  -- compactness of the closed ball in `T_qM`, and a convergent subsequence
  haveI hproper : ProperSpace (TangentSpace I q) := by
    haveI : FiniteDimensional ℝ (TangentSpace I q) := ‹FiniteDimensional ℝ E›
    exact FiniteDimensional.proper ℝ (TangentSpace I q)
  obtain ⟨W, -, φ, hφmono, hφtend⟩ :=
    (isCompact_closedBall (0 : TangentSpace I q) (‖U‖ + 1)).tendsto_subseq
      (fun n => by rw [Metric.mem_closedBall, dist_zero_right]; exact hbound n)
  -- `y n → p`
  have hlim0 : Tendsto (fun n : ℕ => ENNReal.ofReal (((n : ℝ) + 1)⁻¹)) atTop
      (𝓝 (0 : ℝ≥0∞)) := by
    have h1 : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp h1
    simpa [Function.comp_def] using h2
  have hytend : Tendsto y atTop (𝓝 p) := by
    rw [tendsto_def]
    intro s hs
    obtain ⟨c, hc, hcs⟩ := Submission.EDist.setOf_riemannianEDist_lt_subset_nhds (I := I) hs
    have h2 : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (((n : ℝ) + 1)⁻¹) < c :=
      hlim0.eventually (Iio_mem_nhds hc)
    filter_upwards [h2] with n hn
    exact hcs (lt_trans (hy n) hn)
  -- `d p (y n) → 0`
  have hdptend : Tendsto (fun n : ℕ => Manifold.riemannianEDist I p (y n)) atTop
      (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim0
      (fun _ => zero_le) (fun n => (hy n).le)
  -- continuity of `GExp q` and of `z ↦ d p z` give `GExp q W = p`
  have hGtend : Tendsto (fun n : ℕ => Submission.GlobalExp.GExp (cov := cov) hmet q (V (φ n)))
      atTop (𝓝 (Submission.GlobalExp.GExp (cov := cov) hmet q W)) := by
    have hcont : ContinuousAt
        (fun w : TangentSpace I q => Submission.GlobalExp.GExp (cov := cov) hmet q w) W :=
      (Submission.GExpLocalInj.contMDiffAt_GExp_one (cov := cov) hmet q W).continuousAt
    simpa [Function.comp_def] using hcont.tendsto.comp hφtend
  have hdp_Gtend : Tendsto (fun n : ℕ => Manifold.riemannianEDist I p
        (Submission.GlobalExp.GExp (cov := cov) hmet q (V (φ n)))) atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hcongr : (fun n : ℕ => Manifold.riemannianEDist I p
          (Submission.GlobalExp.GExp (cov := cov) hmet q (V (φ n))))
        = fun n : ℕ => Manifold.riemannianEDist I p (y (φ n)) := by
      funext n
      rw [hVexp (φ n)]
    rw [hcongr]
    exact hdptend.comp hφmono.tendsto_atTop
  have hdp_Glim : Tendsto (fun n : ℕ => Manifold.riemannianEDist I p
        (Submission.GlobalExp.GExp (cov := cov) hmet q (V (φ n)))) atTop
      (𝓝 (Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet q W))) :=
    ((Submission.HopfRinow.continuous_riemannianEDist_left (I := I) p).continuousAt).tendsto.comp
      hGtend
  have hzero : Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet q W) = 0 :=
    tendsto_nhds_unique hdp_Glim hdp_Gtend
  have hGp : Submission.GlobalExp.GExp (cov := cov) hmet q W = p :=
    ((Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp hzero).symm
  -- the norms converge, giving `‖W‖ = ‖U‖`
  have hdqtend : Tendsto (fun n : ℕ => Manifold.riemannianEDist I q (y (φ n))) atTop
      (𝓝 (Manifold.riemannianEDist I q p)) :=
    ((Submission.HopfRinow.continuous_riemannianEDist_left (I := I) q).continuousAt).tendsto.comp
      (hytend.comp hφmono.tendsto_atTop)
  have hnormtend : Tendsto (fun n : ℕ => ENNReal.ofReal ‖V (φ n)‖) atTop
      (𝓝 (ENNReal.ofReal ‖W‖)) := by
    have h := (ENNReal.continuous_ofReal.tendsto ‖W‖).comp hφtend.norm
    simpa [Function.comp_def] using h
  have hnormWU : ‖W‖ = ‖U‖ := by
    have hEq : (fun n : ℕ => Manifold.riemannianEDist I q (y (φ n))) =ᶠ[atTop]
        fun n : ℕ => ENNReal.ofReal ‖V (φ n)‖ := by
      filter_upwards with n
      exact hVnorm (φ n)
    have h1 : ENNReal.ofReal ‖W‖ = Manifold.riemannianEDist I q p :=
      tendsto_nhds_unique hnormtend (hdqtend.congr' hEq)
    have h2 := congrArg ENNReal.toReal (h1.trans hqU)
    simpa [ENNReal.toReal_ofReal (norm_nonneg W), ENNReal.toReal_ofReal (norm_nonneg U)] using h2
  -- `W` is another minimising vector, hence equals `U`; but `‖W - U‖ ≥ r`
  have hsub_tend : Tendsto (fun n : ℕ => ‖V (φ n) - U‖) atTop (𝓝 ‖W - U‖) := by
    have h := (hφtend.sub (tendsto_const_nhds (x := U))).norm
    simpa [Function.comp_def] using h
  have hfar : r ≤ ‖W - U‖ :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hsub_tend
      (Eventually.of_forall fun n => hVfar (φ n))
  have hW : W = U := huniq W hGp hnormWU
  rw [hW] at hfar
  simp only [sub_self, norm_zero] at hfar
  linarith

end Work.OddBound.polygon
