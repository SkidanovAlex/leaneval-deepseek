import Mathlib
import Submission.Work.OddBound.sqDistChart.Imports

set_option maxHeartbeats 1000000

namespace Work.OddBound.sqDistChart

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.GlobalExp Submission.InjRadius


/-- **Minimisers cluster near a minimiser, in the chart coordinates of the tangent bundle.**

Let `x₀` be a point with `InjAtLeast hmet x₀ r`, and let `y₀` be at distance `< r` from `x₀`, with
`w` a minimising vector at `x₀`: `GExp x₀ w = y₀` and `d(x₀,y₀) = ‖w‖`. Then in the coordinates of
the tangent-bundle trivialisation at `z`, *every* minimising vector joining a base point `x` close
to `x₀` to a point `y` close to `y₀` clusters near the coordinates of `w`.

The proof is the classical compactness argument (compare
`Work.OddBound.polygon.minimisers_cluster_near_segmentDomain` for the fixed base point, and
`Work.OddBound.polygonValue.joint_inverse_continuity` for the uniform-in-the-base-point version).

* `GExpJointPt.exists_chartFrame` supplies a compact chart window `F.Z` around `x₀` in which the
  chart metric dominates `lam * ‖·‖²`; the radius `εfun n := min (n+1)⁻¹ (c.toReal/2)` is small
  enough that the `x`-witnesses of a counterexample sequence already lie in `F.Z`.
* Suppose the conclusion fails: for every `n` there are `x n`, `y n` and a *minimising* `V n` at
  `x n` with `d(x₀,x n) < εfun n`, `d(y₀,y n) < εfun n` and
  `δ ≤ ‖triv_{x n} V n - triv_{x₀} w‖`.  Since `d(x n, y n) = ‖V n‖` stays bounded, the
  metric lower bound makes the chart coordinate vectors `a n := triv_{x n} V n` a bounded sequence
  in the finite-dimensional space `E`, so a subsequence `a (φ n)` converges to some `a₀`
  (`IsCompact.tendsto_subseq`).
* `GExpJointPt.tendsto_GExp_frameVector` (joint continuity of `GExp` in base point and chart
  velocity) and the convergence of the frame norms identify the limit:
  `GExp x₀ (frameVector z x₀ a₀) = y₀` and `‖frameVector z x₀ a₀‖ = ‖w‖`; the latter is proved by
  squeezing `|‖V n‖ - ‖w‖|` between `± (d(x₀,x n).toReal + d(y₀,y n).toReal) → 0`.
* `hinj` (injectivity of the exponential map at `x₀` on the ball of radius `r`) applied to `w` and
  `frameVector z x₀ a₀` — both of norm `‖w‖ < r` and with the same image — forces
  `frameVector z x₀ a₀ = w`, hence `a₀ = triv_{x₀} w`, contradicting the strict separation `δ`. -/
theorem minimisers_cluster_chartCoord
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {z x₀ : M} (hz : x₀ ∈ (extChartAt I z).source)
    {r : ℝ} (hinj : Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x₀ r)
    {y₀ : M} (hd : Manifold.riemannianEDist I x₀ y₀ < ENNReal.ofReal r)
    {w : TangentSpace I x₀} (hw : Submission.GlobalExp.GExp (cov := cov) hmet x₀ w = y₀)
    (hwn : Manifold.riemannianEDist I x₀ y₀ = ENNReal.ofReal ‖w‖)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ (x : M), Manifold.riemannianEDist I x₀ x < ENNReal.ofReal ε →
      ∀ (y : M), Manifold.riemannianEDist I y₀ y < ENNReal.ofReal ε →
      ∀ (V : TangentSpace I x), x ∈ (extChartAt I z).source →
        Submission.GlobalExp.GExp (cov := cov) hmet x V = y →
        Manifold.riemannianEDist I x y = ENNReal.ofReal ‖V‖ →
        ‖(trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ x V
          - (trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ x₀ w‖ < δ := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  -- the tangent-bundle trivialisation at `z`, in which the conclusion is phrased
  let e := trivializationAt E (TangentSpace I) z
  have hzsrc : x₀ ∈ (chartAt H z).source := by
    simpa only [extChartAt_source] using hz
  -- `0 < r` and `‖w‖ < r`
  have hrpos : 0 < r :=
    ENNReal.ofReal_pos.mp
      (lt_of_le_of_lt (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal ‖w‖) (hwn ▸ hd))
  have hwlt : ‖w‖ < r :=
    (ENNReal.ofReal_lt_ofReal_iff hrpos).mp (by rw [← hwn]; exact hd)
  -- a compact chart window around `x₀` on which the chart metric is comparable to `‖·‖`
  obtain ⟨F⟩ := Submission.GExpJointPt.exists_chartFrame (cov := cov) hmet (z := z) (p := x₀) hzsrc
  have hFZnhds : F.Z ∈ 𝓝 x₀ := F.nhds_of_strict hzsrc (by
    change ‖(extChartAt I z) x₀ - F.x‖ < F.η
    rw [F.hx, sub_self, norm_zero]
    exact F.hη)
  obtain ⟨cc, hcc, hccZ⟩ := Submission.EDist.setOf_riemannianEDist_lt_subset_nhds (I := I) hFZnhds
  have hcc1pos : 0 < min cc 1 := lt_min hcc (by norm_num)
  have hcc1lt : min cc 1 < ⊤ := lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top
  have hcc1Z : {y : M | Manifold.riemannianEDist I x₀ y < min cc 1} ⊆ F.Z := fun y hy =>
    hccZ (lt_of_lt_of_le (show Manifold.riemannianEDist I x₀ y < min cc 1 from hy)
      (min_le_left _ _))
  -- the numerical radius of the cluster neighbourhood
  let εfun : ℕ → ℝ := fun n => min (((n : ℝ) + 1)⁻¹) ((min cc 1).toReal / 2)
  have hεpos : ∀ n, 0 < εfun n := by
    intro n
    refine lt_min (by positivity) ?_
    have h : 0 < (min cc 1).toReal := ENNReal.toReal_pos (ne_of_gt hcc1pos) (ne_of_lt hcc1lt)
    linarith
  have hε_le : ∀ n, εfun n ≤ ((n : ℝ) + 1)⁻¹ := fun n => min_le_left _ _
  have hε_nonneg : ∀ n, 0 ≤ εfun n := fun n => (hεpos n).le
  have hε_ofReal_le : ∀ n, ENNReal.ofReal (εfun n) ≤ min cc 1 := by
    intro n
    have h1 : εfun n ≤ (min cc 1).toReal := by
      have h2 : εfun n ≤ (min cc 1).toReal / 2 := min_le_right _ _
      have h3 : 0 ≤ (min cc 1).toReal := ENNReal.toReal_nonneg
      linarith
    calc ENNReal.ofReal (εfun n) ≤ ENNReal.ofReal (min cc 1).toReal :=
          ENNReal.ofReal_le_ofReal h1
      _ = min cc 1 := ENNReal.ofReal_toReal (ne_of_lt hcc1lt)
  have hε_tend : Tendsto εfun atTop (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      (fun n => hε_nonneg n) (fun n => hε_le n)
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ (x : M) (y : M) (V : TangentSpace I x),
      Manifold.riemannianEDist I x₀ x < ENNReal.ofReal (εfun n) ∧
      Manifold.riemannianEDist I y₀ y < ENNReal.ofReal (εfun n) ∧
      x ∈ (extChartAt I z).source ∧
      Submission.GlobalExp.GExp (cov := cov) hmet x V = y ∧
      Manifold.riemannianEDist I x y = ENNReal.ofReal ‖V‖ ∧
      δ ≤ ‖e.continuousLinearMapAt ℝ x V - e.continuousLinearMapAt ℝ x₀ w‖ := by
    intro n
    obtain ⟨x, hx, y, hy, V, hs, hge, hn, hf⟩ := hcon (εfun n) (hεpos n)
    exact ⟨x, y, V, hx, hy, hs, hge, hn, hf⟩
  choose x y V hxε hyε hxsrc hGexp hVnorm hVfar using hseq
  let a : ℕ → E := fun n => e.continuousLinearMapAt ℝ (x n) (V n)
  -- small extended distances to `εfun n` give convergence
  have key : ∀ {f : ℕ → M} {p : M},
      (∀ n, Manifold.riemannianEDist I p (f n) < ENNReal.ofReal (εfun n)) →
      Tendsto f atTop (𝓝 p) := by
    intro f p hf
    refine Submission.GExpJointPt.tendsto_of_eventually_edist_lt (I := I) (M := M) ?_
    intro ε hε
    have hsmall : ∀ᶠ n : ℕ in atTop, εfun n < ε := hε_tend.eventually (Iio_mem_nhds hε)
    filter_upwards [hsmall] with n hn
    exact lt_of_lt_of_le (hf n) (ENNReal.ofReal_le_ofReal hn.le)
  have hxT : Tendsto x atTop (𝓝 x₀) := key hxε
  have hyT : Tendsto y atTop (𝓝 y₀) := key hyε
  -- the base points of the counterexamples lie in the chart window
  have hxZ : ∀ n, x n ∈ F.Z := fun n => hcc1Z (lt_of_lt_of_le (hxε n) (hε_ofReal_le n))
  have hxchart : ∀ n, x n ∈ (chartAt H z).source := fun n => F.hZsrc (hxZ n)
  -- the chart coordinates of `V n`
  have hfv : ∀ n, frameVector (I := I) z (x n) (a n) = V n := by
    intro n
    have hb : x n ∈ e.baseSet := by
      change x n ∈ (trivializationAt E (TangentSpace I) z).baseSet
      rw [TangentBundle.trivializationAt_baseSet]
      simpa only [extChartAt_source] using hxsrc n
    have h1 := Bundle.Trivialization.symmL_continuousLinearMapAt (R := ℝ) e hb (V n)
    simpa only [Submission.Geodesic.frameVector] using h1
  -- the fibre norms are bounded
  have hVbd : ∀ n, ‖V n‖ ≤ ‖w‖ + 2 := by
    intro n
    have h1 : Manifold.riemannianEDist I (x n) x₀ < ENNReal.ofReal (εfun n) := by
      rw [Manifold.riemannianEDist_comm]; exact hxε n
    have h2 : Manifold.riemannianEDist I x₀ (y n)
        < ENNReal.ofReal ‖w‖ + ENNReal.ofReal (εfun n) := by
      calc Manifold.riemannianEDist I x₀ (y n)
          ≤ Manifold.riemannianEDist I x₀ y₀ + Manifold.riemannianEDist I y₀ (y n) :=
            Manifold.riemannianEDist_triangle
        _ < ENNReal.ofReal ‖w‖ + ENNReal.ofReal (εfun n) :=
            ENNReal.add_lt_add_of_le_of_lt (ne_top_of_lt hd) hwn.le (hyε n)
    have h3 : Manifold.riemannianEDist I (x n) (y n)
        ≤ ENNReal.ofReal (εfun n) + (ENNReal.ofReal ‖w‖ + ENNReal.ofReal (εfun n)) :=
      le_trans Manifold.riemannianEDist_triangle (add_le_add h1.le h2.le)
    have h3' : ENNReal.ofReal (εfun n) + (ENNReal.ofReal ‖w‖ + ENNReal.ofReal (εfun n))
        = ENNReal.ofReal (εfun n + (‖w‖ + εfun n)) := by
      rw [← ENNReal.ofReal_add (norm_nonneg w) (hε_nonneg n),
        ← ENNReal.ofReal_add (hε_nonneg n) (by positivity)]
    have h4 : ENNReal.ofReal ‖V n‖ ≤ ENNReal.ofReal (εfun n + (‖w‖ + εfun n)) := by
      rw [← hVnorm n, ← h3']
      exact h3
    have h5 : ‖V n‖ ≤ εfun n + (‖w‖ + εfun n) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h4
    have h6 : εfun n + (‖w‖ + εfun n) ≤ 1 + (‖w‖ + 1) := by
      have hle1 : εfun n ≤ 1 := by
        refine le_trans (hε_le n) (inv_le_one_of_one_le₀ ?_)
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    linarith
  -- coordinates of the `V n` are bounded, so a subsequence converges
  have ha_mem : ∀ n, a n ∈ Metric.closedBall (0 : E) ((‖w‖ + 2) / Real.sqrt F.lam) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    have hlam_pos : 0 < Real.sqrt F.lam := Real.sqrt_pos.mpr F.hlam
    have hgr := (F.hbnd (x n) (hxZ n) (a n)).1
    have h1 : Real.sqrt F.lam * ‖a n‖ ≤ ‖V n‖ := by
      have h2 : Real.sqrt F.lam * ‖a n‖ = Real.sqrt (F.lam * ‖a n‖ ^ 2) := by
        rw [Real.sqrt_mul F.hlam.le, Real.sqrt_sq (norm_nonneg _)]
      rw [h2]
      calc Real.sqrt (F.lam * ‖a n‖ ^ 2)
          ≤ Real.sqrt (Submission.ChartConnection.chartGram (I := I) z (x n) (a n) (a n)) :=
            Real.sqrt_le_sqrt hgr
        _ = ‖frameVector (I := I) z (x n) (a n)‖ :=
            (Submission.GExpFlow.norm_frameVector (I := I) (z₀ := z) (q := x n) (a n)).symm
        _ = ‖V n‖ := by rw [hfv n]
    calc ‖a n‖ = Real.sqrt F.lam * ‖a n‖ / Real.sqrt F.lam :=
          (mul_div_cancel_left₀ ‖a n‖ hlam_pos.ne').symm
      _ ≤ (‖w‖ + 2) / Real.sqrt F.lam :=
          div_le_div_of_nonneg_right (le_trans h1 (hVbd n)) hlam_pos.le
  haveI hproper : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨a₀, -, φ, hφmono, hφtend⟩ :=
    (isCompact_closedBall (0 : E) ((‖w‖ + 2) / Real.sqrt F.lam)).tendsto_subseq ha_mem
  -- joint continuity of `GExp` in base point and chart velocity
  have hxφ : Tendsto (fun n => x (φ n)) atTop (𝓝 x₀) := hxT.comp hφmono.tendsto_atTop
  have hyφ : Tendsto (fun n => y (φ n)) atTop (𝓝 y₀) := hyT.comp hφmono.tendsto_atTop
  have hGtend : Tendsto (fun n => Submission.GlobalExp.GExp (cov := cov) hmet (x (φ n))
      (frameVector (I := I) z (x (φ n)) (a (φ n)))) atTop
      (𝓝 (Submission.GlobalExp.GExp (cov := cov) hmet x₀ (frameVector (I := I) z x₀ a₀))) :=
    Submission.GExpJointPt.tendsto_GExp_frameVector (cov := cov) hmet htor hzsrc hxφ hφtend
  have hcongr : (fun n => Submission.GlobalExp.GExp (cov := cov) hmet (x (φ n))
      (frameVector (I := I) z (x (φ n)) (a (φ n)))) = fun n => y (φ n) := by
    funext n
    rw [hfv (φ n), hGexp (φ n)]
  have hGlim : Submission.GlobalExp.GExp (cov := cov) hmet x₀ (frameVector (I := I) z x₀ a₀)
      = y₀ := tendsto_nhds_unique hGtend (hcongr.symm ▸ hyφ)
  -- the norms of the `V (φ n)` converge to `‖w‖`
  have hnorm_gen : Tendsto (fun n => ‖V (φ n)‖) atTop (𝓝 ‖w‖) := by
    have hlim_eps : Tendsto (fun n => εfun (φ n)) atTop (𝓝 (0 : ℝ)) :=
      hε_tend.comp hφmono.tendsto_atTop
    have hA0 : Tendsto (fun n => (Manifold.riemannianEDist I x₀ (x (φ n))).toReal) atTop
        (𝓝 (0 : ℝ)) := by
      refine squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_) hlim_eps
      calc (Manifold.riemannianEDist I x₀ (x (φ n))).toReal
          ≤ (ENNReal.ofReal (εfun (φ n))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (le_of_lt (hxε (φ n)))
        _ = εfun (φ n) := ENNReal.toReal_ofReal (hε_nonneg (φ n))
    have hB0 : Tendsto (fun n => (Manifold.riemannianEDist I y₀ (y (φ n))).toReal) atTop
        (𝓝 (0 : ℝ)) := by
      refine squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_) hlim_eps
      calc (Manifold.riemannianEDist I y₀ (y (φ n))).toReal
          ≤ (ENNReal.ofReal (εfun (φ n))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (le_of_lt (hyε (φ n)))
        _ = εfun (φ n) := ENNReal.toReal_ofReal (hε_nonneg (φ n))
    -- two-sided bounds for `‖V n‖` in terms of the distance to `x₀` resp. `y₀`
    have hup : ∀ n, ‖V n‖ ≤ (Manifold.riemannianEDist I x₀ (x n)).toReal
        + (‖w‖ + (Manifold.riemannianEDist I y₀ (y n)).toReal) := by
      intro n
      have hfinA : Manifold.riemannianEDist I (x n) x₀ ≠ ⊤ := ne_top_of_lt (by
        rw [Manifold.riemannianEDist_comm]; exact hxε n)
      have hfinB : Manifold.riemannianEDist I y₀ (y n) ≠ ⊤ := ne_top_of_lt (hyε n)
      have hfinD : Manifold.riemannianEDist I x₀ y₀ ≠ ⊤ := ne_top_of_lt hd
      have hfinDB : Manifold.riemannianEDist I x₀ y₀ + Manifold.riemannianEDist I y₀ (y n)
          ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hfinD, hfinB⟩
      have hfin : Manifold.riemannianEDist I (x n) x₀ + (Manifold.riemannianEDist I x₀ y₀
          + Manifold.riemannianEDist I y₀ (y n)) ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨hfinA, hfinDB⟩
      have h3 : Manifold.riemannianEDist I (x n) (y n)
          ≤ Manifold.riemannianEDist I (x n) x₀ + (Manifold.riemannianEDist I x₀ y₀
              + Manifold.riemannianEDist I y₀ (y n)) :=
        le_trans Manifold.riemannianEDist_triangle (add_le_add le_rfl Manifold.riemannianEDist_triangle)
      have h4 := ENNReal.toReal_mono hfin h3
      rw [hVnorm n, ENNReal.toReal_ofReal (norm_nonneg (V n)),
        ENNReal.toReal_add hfinA hfinDB, ENNReal.toReal_add hfinD hfinB,
        hwn, ENNReal.toReal_ofReal (norm_nonneg w)] at h4
      rw [congrArg ENNReal.toReal (Manifold.riemannianEDist_comm (I := I) (x := x n) (y := x₀))]
        at h4
      linarith
    have hlow : ∀ n, ‖w‖ ≤ (Manifold.riemannianEDist I x₀ (x n)).toReal
        + (‖V n‖ + (Manifold.riemannianEDist I y₀ (y n)).toReal) := by
      intro n
      have hfinA : Manifold.riemannianEDist I x₀ (x n) ≠ ⊤ := ne_top_of_lt (hxε n)
      have hfinF : Manifold.riemannianEDist I (x n) (y n) ≠ ⊤ := by
        rw [hVnorm n]; exact ENNReal.ofReal_ne_top
      have hfinB : Manifold.riemannianEDist I (y n) y₀ ≠ ⊤ := by
        rw [Manifold.riemannianEDist_comm]; exact ne_top_of_lt (hyε n)
      have hfinFB : Manifold.riemannianEDist I (x n) (y n) + Manifold.riemannianEDist I (y n) y₀
          ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hfinF, hfinB⟩
      have hfin : Manifold.riemannianEDist I x₀ (x n) + (Manifold.riemannianEDist I (x n) (y n)
          + Manifold.riemannianEDist I (y n) y₀) ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨hfinA, hfinFB⟩
      have h3 : Manifold.riemannianEDist I x₀ y₀
          ≤ Manifold.riemannianEDist I x₀ (x n) + (Manifold.riemannianEDist I (x n) (y n)
              + Manifold.riemannianEDist I (y n) y₀) :=
        le_trans Manifold.riemannianEDist_triangle (add_le_add le_rfl Manifold.riemannianEDist_triangle)
      have h4 := ENNReal.toReal_mono hfin h3
      rw [hwn, ENNReal.toReal_ofReal (norm_nonneg w),
        ENNReal.toReal_add hfinA hfinFB, ENNReal.toReal_add hfinF hfinB,
        hVnorm n, ENNReal.toReal_ofReal (norm_nonneg (V n))] at h4
      rw [congrArg ENNReal.toReal (Manifold.riemannianEDist_comm (I := I) (x := y n) (y := y₀))]
        at h4
      linarith
    have habs : ∀ n, |‖V (φ n)‖ - ‖w‖|
        ≤ (Manifold.riemannianEDist I x₀ (x (φ n))).toReal
          + (Manifold.riemannianEDist I y₀ (y (φ n))).toReal := by
      intro n
      have hu := hup (φ n)
      have hl := hlow (φ n)
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have hc0 : Tendsto (fun n => (Manifold.riemannianEDist I x₀ (x (φ n))).toReal
        + (Manifold.riemannianEDist I y₀ (y (φ n))).toReal) atTop (𝓝 0) := by
      simpa using hA0.add hB0
    have hsq := squeeze_zero (fun n => abs_nonneg _) habs hc0
    exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa [Real.norm_eq_abs] using hsq)
  have hframe_tend : Tendsto (fun n => ‖frameVector (I := I) z (x (φ n)) (a (φ n))‖) atTop
      (𝓝 ‖frameVector (I := I) z x₀ a₀‖) := by
    have hcont := Submission.ChartBounds.continuousAt_chartGram_prod (I := I) z hzsrc a₀
    have hpair : Tendsto (fun n => (x (φ n), a (φ n))) atTop (𝓝 (x₀, a₀)) :=
      (Prod.tendsto_iff (fun n => (x (φ n), a (φ n))) (x₀, a₀)).mpr ⟨hxφ, hφtend⟩
    have h1 : Tendsto (fun n => Submission.ChartConnection.chartGram (I := I) z (x (φ n))
        (a (φ n)) (a (φ n))) atTop
        (𝓝 (Submission.ChartConnection.chartGram (I := I) z x₀ a₀ a₀)) :=
      hcont.tendsto.comp hpair
    have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp h1
    simpa only [Function.comp_def, Submission.GExpFlow.norm_frameVector] using h2
  have hframeV : Tendsto (fun n => ‖V (φ n)‖) atTop (𝓝 ‖frameVector (I := I) z x₀ a₀‖) :=
    hframe_tend.congr' (Filter.Eventually.of_forall fun n => by rw [hfv (φ n)])
  have hwnorm : ‖frameVector (I := I) z x₀ a₀‖ = ‖w‖ := tendsto_nhds_unique hframeV hnorm_gen
  -- uniqueness of the minimising vector at `x₀`, using only injectivity there
  have hfv0w : frameVector (I := I) z x₀ a₀ = w :=
    (hinj w (frameVector (I := I) z x₀ a₀) hwlt (by rw [hwnorm]; exact hwlt)
      (hw.trans hGlim.symm)).symm
  have ha₀ : a₀ = e.continuousLinearMapAt ℝ x₀ w := by
    have hb : x₀ ∈ e.baseSet := by
      change x₀ ∈ (trivializationAt E (TangentSpace I) z).baseSet
      rw [TangentBundle.trivializationAt_baseSet]
      exact hzsrc
    have h1 := Bundle.Trivialization.continuousLinearMapAt_symmL (R := ℝ) e hb a₀
    rw [← hfv0w]
    exact h1.symm
  -- contradiction with the strict separation along the sequence
  have hfar : δ ≤ ‖a₀ - e.continuousLinearMapAt ℝ x₀ w‖ :=
    le_of_tendsto_of_tendsto' (tendsto_const_nhds : Tendsto (fun _ : ℕ => δ) atTop (𝓝 δ))
      ((hφtend.sub (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => e.continuousLinearMapAt ℝ x₀ w) atTop
          (𝓝 (e.continuousLinearMapAt ℝ x₀ w)))).norm)
      (fun n => hVfar (φ n))
  rw [ha₀, sub_self, norm_zero] at hfar
  linarith

end Work.OddBound.sqDistChart