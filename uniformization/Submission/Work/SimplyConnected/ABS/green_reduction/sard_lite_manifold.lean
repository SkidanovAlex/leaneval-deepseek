import Submission.ChartBallBarrier
import Submission.Work.SimplyConnected.ABS.green_reduction.sard_cubic
import Submission.Work.SimplyConnected.ABS.green_reduction.sard_ingredients
import Submission.Work.SimplyConnected.ABS.green_reduction.sard_covering

/-!
# Sard-lite on a Riemann surface

This module transports the planar Sard-lite machinery (`sard_covering.lean`, `sard_cubic.lean`) to
an arbitrary non-compact `ℂ`-charted surface: for a `C^∞` function `g : X → ℝ` and a compact set
`K`, the critical values of `g` on `K` are contained in finitely many intervals of arbitrarily small
total length.  From this, a *regular* level of `g` in any prescribed interval exists, which is the
last missing input of the Sard route to
`green_reduction.exists_barrier_regular_precompact_region` (see `sard_lite_assembly.lean`).

The three geometric inputs are:

* `contDiffAt_chartPullback`: the pull-back of a `C^∞` function by a chart is `C^∞` (hence `C^3`)
  at the image of a point — this is the `contMDiffAt_iff` unfolding, `chartAt_self_eq` for the
  target ℝ and `extChartAt = chartAt` for the source;
* `exists_ball_iteratedFDeriv_bound`: a `C^3` function at a point is `C^3` on a ball around it, with
  a bound for its third derivative there (the bound comes from compactness, on half the radius);
* `cubic_critical_estimate` + `exists_intervals_cover_criticalValues`, the planar core.

The chart-independence of "critical point" (`fderiv_chartPullback_self_eq_zero`) is needed because
the planar covering is applied in the charts of a *finite cover*, while the final statement is about
the preferred chart at each critical point.
-/

open Set Metric Filter
open scoped Topology Manifold ContDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.SimplyConnected.ABS.green_reduction

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The shifted chart pull-back** of `g` at `x`: the function of the chart coordinate `w` around
the image `(chartAt ℂ x) x` of `x`.  All the planar machinery is applied to this function. -/
def chartPullbackShift (g : X → ℝ) (x : X) : ℂ → ℝ :=
  fun w => g ((chartAt ℂ x).symm ((chartAt ℂ x) x + w))

theorem chartPullbackShift_apply (g : X → ℝ) (x : X) (w : ℂ) :
    chartPullbackShift g x w = g ((chartAt ℂ x).symm ((chartAt ℂ x) x + w)) := rfl

/-- **The chart pull-back of a `C^∞` function is `C^3` at the image of the point.** -/
theorem contDiffAt_chartPullback {g : X → ℝ}
    (hg : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ g) (x : X) :
    ContDiffAt ℝ 3 (fun z : ℂ => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x) := by
  have h := (contMDiffAt_iff.mp (hg x)).2
  simp only [mfld_simps] at h
  simp only [Function.comp_def, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq] at h
  exact contDiffWithinAt_univ.mp (h.of_le (by decide))

/-- **The shifted chart pull-back is `C^3` at the origin.** -/
theorem contDiffAt_chartPullbackShift {g : X → ℝ}
    (hg : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ g) (x : X) :
    ContDiffAt ℝ 3 (chartPullbackShift g x) 0 := by
  have h := contDiffAt_chartPullback hg x
  have h2 : ContDiffAt ℝ 3 (fun w : ℂ => (chartAt ℂ x) x + w) 0 :=
    (contDiff_const.add contDiff_id).contDiffAt
  have h' : ContDiffAt ℝ 3 (fun z : ℂ => g ((chartAt ℂ x).symm z))
      ((fun w : ℂ => (chartAt ℂ x) x + w) 0) := by simpa using h
  have h3 := h'.comp 0 h2
  exact h3

/-- **A `C^3` function at a point is `C^3` on a ball around it, where its third derivative is
bounded.** -/
theorem exists_ball_iteratedFDeriv_bound {h : ℂ → ℝ} {a : ℂ} (ha : ContDiffAt ℝ 3 h a) :
    ∃ (ρ C : ℝ), 0 < ρ ∧ 0 ≤ C ∧ ContDiffOn ℝ 3 h (Metric.ball a ρ) ∧
      (∀ z ∈ Metric.ball a ρ, ‖iteratedFDeriv ℝ 3 h z‖ ≤ C) := by
  obtain ⟨u, hu, hcu⟩ := ha.contDiffOn (m := 3) le_rfl (by simp)
  obtain ⟨ρ₁, hρ₁, hρ₁u⟩ := Metric.mem_nhds_iff.mp hu
  have hcd : ContDiffOn ℝ 3 h (Metric.ball a (ρ₁ / 2)) :=
    hcu.mono ((Metric.ball_subset_ball (by linarith)).trans hρ₁u)
  have hcont : ContinuousOn (iteratedFDeriv ℝ 3 h) (Metric.ball a (ρ₁ / 2)) :=
    ContinuousOn.continuousOn_iteratedFDeriv hcd Metric.isOpen_ball (by decide)
  obtain ⟨C, hC⟩ := (isCompact_closedBall a (ρ₁ / 4)).exists_bound_of_continuousOn
    (hcont.mono (Metric.closedBall_subset_ball (by linarith)))
  refine ⟨ρ₁ / 4, max C 0, by linarith, le_max_right _ _, ?_, ?_⟩
  · exact hcu.mono ((Metric.ball_subset_ball (by linarith)).trans hρ₁u)
  · intro z hz
    exact (hC z (Metric.ball_subset_closedBall hz)).trans (le_max_left _ _)


/-! ## Chart independence of criticality -/

/-- **Chart independence of criticality.**  If the pull-back of `g` in the preferred chart at `p`
has vanishing derivative at `(chartAt ℂ p) p`, then the pull-back in any chart at `y` whose source
contains `p` has vanishing derivative at `(chartAt ℂ y) p`.

This is the direction needed to compare the critical points found by the planar covering argument
(run in the charts of a finite cover) with the critical points of the final statement (expressed in
the preferred chart at each point).  The proof is the chain rule along the *inverse* transition
`(chartAt ℂ p) ∘ (chartAt ℂ y).symm`, which is analytic (hence differentiable), so no surjectivity
argument is needed. -/
theorem fderiv_chartPullback_self_eq_zero {g : X → ℝ} {p y : X}
    (hy : p ∈ (chartAt ℂ y).source)
    (hd : DifferentiableAt ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p))
    (h0 : fderiv ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) = 0) :
    fderiv ℝ (fun z : ℂ => g ((chartAt ℂ y).symm z)) ((chartAt ℂ y) p) = 0 := by
  classical
  have hza : (chartAt ℂ y) p ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hy
  have hzd : (chartAt ℂ y).symm ((chartAt ℂ y) p) = p := (chartAt ℂ y).left_inv hy
  have hpcl : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have hzs : (chartAt ℂ y) p ∈ ((chartAt ℂ y).symm.trans (chartAt ℂ p)).source := by
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨hza, by rw [hzd]; exact hpcl⟩
  -- the transition is analytic, hence differentiable
  have hTana : AnalyticAt ℂ (fun w : ℂ => (chartAt ℂ p) ((chartAt ℂ y).symm w))
      ((chartAt ℂ y) p) := by
    have hbase := Submission.analyticAt_transition_of_mem_atlas (c := chartAt ℂ p)
      (d := chartAt ℂ y) (chart_mem_atlas ℂ p) (chart_mem_atlas ℂ y)
      ((chartAt ℂ y) p) hza (by rw [hzd]; exact hpcl)
    refine hbase.congr ?_
    filter_upwards [((chartAt ℂ y).symm.trans (chartAt ℂ p)).open_source.mem_nhds hzs] with w _
    simp only [OpenPartialHomeomorph.trans_apply]
  have hTdiff : DifferentiableAt ℝ (fun w : ℂ => (chartAt ℂ p) ((chartAt ℂ y).symm w))
      ((chartAt ℂ y) p) :=
    ((hTana.differentiableAt.hasDerivAt.hasFDerivAt).restrictScalars ℝ).differentiableAt
  -- the two pull-backs agree near `(chartAt ℂ y) p`
  have hev : (fun w : ℂ => g ((chartAt ℂ y).symm w)) =ᶠ[𝓝 ((chartAt ℂ y) p)]
      (fun w : ℂ => g ((chartAt ℂ p).symm ((chartAt ℂ p) ((chartAt ℂ y).symm w)))) := by
    filter_upwards [((chartAt ℂ y).symm.trans (chartAt ℂ p)).open_source.mem_nhds hzs]
      with w hw
    exact (congrArg g ((chartAt ℂ p).left_inv hw.2)).symm
  -- the chain rule
  have hcomp : fderiv ℝ (fun w : ℂ => g ((chartAt ℂ p).symm ((chartAt ℂ p) ((chartAt ℂ y).symm w))))
        ((chartAt ℂ y) p)
      = (fderiv ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p)).comp
        (fderiv ℝ (fun w : ℂ => (chartAt ℂ p) ((chartAt ℂ y).symm w)) ((chartAt ℂ y) p)) := by
    have hF' : HasFDerivAt (fun z : ℂ => g ((chartAt ℂ p).symm z))
        (fderiv ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p))
        ((fun w : ℂ => (chartAt ℂ p) ((chartAt ℂ y).symm w)) ((chartAt ℂ y) p)) := by
      have hTz : (fun w : ℂ => (chartAt ℂ p) ((chartAt ℂ y).symm w)) ((chartAt ℂ y) p)
          = (chartAt ℂ p) p := by
        show (chartAt ℂ p) ((chartAt ℂ y).symm ((chartAt ℂ y) p)) = (chartAt ℂ p) p
        rw [hzd]
      rw [hTz]
      exact hd.hasFDerivAt
    exact (hF'.comp ((chartAt ℂ y) p) hTdiff.hasFDerivAt).fderiv
  rw [hev.fderiv_eq, hcomp, h0]
  ext v
  simp

/-! ## The local Sard datum in a chart -/

/-- **Local Sard-lite in a chart.**  For a smooth `g` and a point `x` there is a radius `r > 0`
(chart coordinate around `(chartAt ℂ x) x`, small enough that the closed chart ball of radius `2r`
lies in the chart target) such that, for every `ε > 0`, the critical values of `g` on the closed
chart ball of radius `r` around `x` are covered by finitely many intervals of total length `< ε`.

The criticality is expressed in the chart at `x` itself, and the critical *point* is identified
through the chart. -/
theorem exists_localSardData {g : X → ℝ}
    (hg : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ g) (x : X) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall ((chartAt ℂ x) x) (2 * r) ⊆ (chartAt ℂ x).target ∧
      ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (l u : Fin n → ℝ), (∀ i, l i ≤ u i) ∧
        (∑ i, (u i - l i)) < ε ∧
        ∀ p : X, p ∈ (chartAt ℂ x).source →
          (chartAt ℂ x) p ∈ Metric.closedBall ((chartAt ℂ x) x) r →
          fderiv ℝ (fun z : ℂ => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) p) = 0 →
          ∃ i, g p ∈ Set.Icc (l i) (u i) := by
  obtain ⟨ρ₀, C₀, hρ₀, hC₀, hcd, hbd⟩ := exists_ball_iteratedFDeriv_bound (contDiffAt_chartPullbackShift hg x)
  obtain ⟨ρ₁, hρ₁, hsub₁⟩ : ∃ ρ₁ : ℝ, 0 < ρ₁ ∧
      Metric.closedBall ((chartAt ℂ x) x) ρ₁ ⊆ (chartAt ℂ x).target := by
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp
      ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))
    exact ⟨ρ / 2, half_pos hρ, (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩
  set r : ℝ := min (ρ₀ / 3) (ρ₁ / 2) with hrdef
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have h2ρ₀ : 2 * r < ρ₀ := by
    have h : r ≤ ρ₀ / 3 := min_le_left _ _
    linarith
  have h2ρ₁ : 2 * r ≤ ρ₁ := by
    have h : r ≤ ρ₁ / 2 := min_le_right _ _
    linarith
  refine ⟨r, hr, (Metric.closedBall_subset_closedBall h2ρ₁).trans hsub₁, ?_⟩
  intro ε hε
  have hcd' : ContDiffOn ℝ 3 (chartPullbackShift g x) (Metric.ball 0 (2 * r)) :=
    hcd.mono (Metric.ball_subset_ball (le_of_lt h2ρ₀))
  have hb' : ∀ z ∈ Metric.closedBall (0:ℂ) r,
      ‖iteratedFDeriv ℝ 3 (chartPullbackShift g x) z‖ ≤ C₀ := fun z hz =>
    hbd z (Metric.closedBall_subset_ball (by linarith) hz)
  obtain ⟨K, hK0, hK⟩ := cubic_critical_estimate (f := chartPullbackShift g x) (x₀ := 0)
    (r := r) (r' := 2 * r) (C := C₀) hr (by linarith) hcd' hb'
  have hK' : ∀ u : ℂ, ‖u‖ ≤ r → fderiv ℝ (chartPullbackShift g x) u = 0 →
      ∀ v : ℂ, ‖v‖ ≤ r → fderiv ℝ (chartPullbackShift g x) v = 0 →
      |chartPullbackShift g x v - chartPullbackShift g x u| ≤ K * ‖v - u‖ ^ 3 := by
    intro u hu huu v hv hvv
    exact hK u (by rwa [Metric.mem_closedBall, dist_zero_right]) huu v
      (by rwa [Metric.mem_closedBall, dist_zero_right]) hvv
  obtain ⟨n, l, u, hlu, hsum, hcov⟩ := exists_intervals_cover_criticalValues
    (f := chartPullbackShift g x) (R := r) (C := K) (ε := ε) (le_of_lt hr) hK0 hε hK'
  refine ⟨n, l, u, hlu, hsum, ?_⟩
  intro p hp hpr hcrit
  set w : ℂ := (chartAt ℂ x) p - (chartAt ℂ x) x with hwdef
  have hwball : ‖w‖ ≤ r := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hpr
    rw [hwdef]
    exact hpr
  have hweq : (chartAt ℂ x) x + w = (chartAt ℂ x) p := by
    rw [hwdef]; ring
  have hleft : (chartAt ℂ x).symm ((chartAt ℂ x) p) = p := (chartAt ℂ x).left_inv hp
  have hcrit' : fderiv ℝ (chartPullbackShift g x) w = 0 := by
    have h1 : fderiv ℝ (chartPullbackShift g x) w
        = fderiv ℝ (fun z : ℂ => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x + w) := by
      show fderiv ℝ (fun u : ℂ => (fun z : ℂ => g ((chartAt ℂ x).symm z))
        ((chartAt ℂ x) x + u)) w = _
      exact fderiv_comp_add_left (𝕜 := ℝ) (f := fun z : ℂ => g ((chartAt ℂ x).symm z))
        ((chartAt ℂ x) x)
    rw [h1, hweq]
    exact hcrit
  have hvals : chartPullbackShift g x w = g p := by
    show g ((chartAt ℂ x).symm ((chartAt ℂ x) x + w)) = g p
    rw [hweq, hleft]
  obtain ⟨i, hi⟩ := hcov w hwball hcrit'
  exact ⟨i, by rwa [hvals] at hi⟩


/-! ## Concatenating finitely many interval families -/

/-- **Concatenation of interval families.**  A finite family of interval families, the `i`-th
indexed by `Fin (n i)`, can be concatenated into a single `Fin N`-indexed family with the same total
length; the equivalence `e` records which index of the concatenated family a given `(i, j)`
corresponds to, so that covering statements transport. -/
theorem exists_fin_intervals_of_sigma {ι : Type*} [Fintype ι] (n : ι → ℕ)
    (l u : ∀ i, Fin (n i) → ℝ) (hlu : ∀ i j, l i j ≤ u i j) :
    ∃ (N : ℕ) (l' u' : Fin N → ℝ),
      (∀ k, l' k ≤ u' k) ∧
      (∑ k, (u' k - l' k)) = ∑ i, ∑ j, (u i j - l i j) ∧
      ∀ (i : ι) (j : Fin (n i)) (v : ℝ), v ∈ Set.Icc (l i j) (u i j) →
        ∃ k, v ∈ Set.Icc (l' k) (u' k) := by
  classical
  set e : (Σ i, Fin (n i)) ≃ Fin (Fintype.card (Σ i, Fin (n i))) :=
    Fintype.equivFin (Σ i, Fin (n i)) with he
  have hl : ∀ s : Σ i, Fin (n i), l (e.symm (e s)).1 (e.symm (e s)).2 = l s.1 s.2 :=
    fun s => congrArg (fun t : Σ i, Fin (n i) => l t.1 t.2) (Equiv.symm_apply_apply e s)
  have hu : ∀ s : Σ i, Fin (n i), u (e.symm (e s)).1 (e.symm (e s)).2 = u s.1 s.2 :=
    fun s => congrArg (fun t : Σ i, Fin (n i) => u t.1 t.2) (Equiv.symm_apply_apply e s)
  refine ⟨Fintype.card (Σ i, Fin (n i)), fun k => l (e.symm k).1 (e.symm k).2,
    fun k => u (e.symm k).1 (e.symm k).2, ?_, ?_, ?_⟩
  · intro k
    exact hlu _ _
  · have h1 : (∑ k : Fin (Fintype.card (Σ i, Fin (n i))),
        (u (e.symm k).1 (e.symm k).2 - l (e.symm k).1 (e.symm k).2))
        = ∑ s : Σ i, Fin (n i), (u s.1 s.2 - l s.1 s.2) := by
      rw [← Equiv.sum_comp e (fun k => u (e.symm k).1 (e.symm k).2 - l (e.symm k).1 (e.symm k).2)]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hu s, hl s]
    rw [h1, Fintype.sum_sigma]
  · intro i j v hv
    refine ⟨e ⟨i, j⟩, ?_⟩
    show v ∈ Set.Icc (l (e.symm (e ⟨i, j⟩)).1 (e.symm (e ⟨i, j⟩)).2)
      (u (e.symm (e ⟨i, j⟩)).1 (e.symm (e ⟨i, j⟩)).2)
    rw [hu ⟨i, j⟩, hl ⟨i, j⟩]
    exact hv

/-! ## Sard-lite on a surface -/

/-- **Sard-lite on a surface.**  For a `C^∞` function `g` on a surface and a compact set `K`, the
critical values of `g` on `K` are covered by finitely many intervals of total length `< ε`.

The criticality is expressed in the preferred chart at the critical point.  The proof covers
`K ∪ {x₀}` by finitely many *open* chart balls coming from `exists_localSardData`, applies the local
planar statement in each of them with `ε` divided by the number of charts, and concatenates the
families.  Chart independence (`fderiv_chartPullback_self_eq_zero`) is what lets the local statement
about the chart at the centre of a ball be used at a critical point of that ball. -/
theorem exists_intervals_cover_criticalValues_of_contMDiff {g : X → ℝ}
    (hg : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ g)
    {K : Set X} (hK : IsCompact K) (x₀ : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (l u : Fin n → ℝ), (∀ i, l i ≤ u i) ∧ (∑ i, (u i - l i)) < ε ∧
      ∀ p ∈ K, fderiv ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) = 0 →
        ∃ i, g p ∈ Set.Icc (l i) (u i) := by
  classical
  have hdat : ∀ z : X, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall ((chartAt ℂ z) z) (2 * r) ⊆ (chartAt ℂ z).target ∧
      ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (l u : Fin n → ℝ), (∀ i, l i ≤ u i) ∧
        (∑ i, (u i - l i)) < ε ∧
        ∀ p : X, p ∈ (chartAt ℂ z).source →
          (chartAt ℂ z) p ∈ Metric.closedBall ((chartAt ℂ z) z) r →
          fderiv ℝ (fun w : ℂ => g ((chartAt ℂ z).symm w)) ((chartAt ℂ z) p) = 0 →
          ∃ i, g p ∈ Set.Icc (l i) (u i) := fun z => exists_localSardData hg z
  choose r hrpos hrtgt hloc using hdat
  -- the cover of `K ∪ {x₀}` by the open chart balls
  have hcov : K ∪ {x₀} ⊆ ⋃ z : X,
      Submission.chartBall (chartAt ℂ z) ((chartAt ℂ z) z) (r z) := by
    intro p hp
    exact Set.mem_iUnion.mpr ⟨p, Submission.mem_chartBall.mpr
      ⟨mem_chart_source ℂ p, by rw [Metric.mem_ball, dist_self]; exact hrpos p⟩⟩
  obtain ⟨t, ht⟩ := (hK.union isCompact_singleton).elim_finite_subcover
    (fun z : X => Submission.chartBall (chartAt ℂ z) ((chartAt ℂ z) z) (r z))
    (fun z => Submission.chartBall_isOpen _ _ _) hcov
  have htne : t.Nonempty := by
    obtain ⟨z, hz, -⟩ := Set.mem_iUnion₂.mp
      (ht (Set.mem_union_right K (Set.mem_singleton x₀)))
    exact ⟨z, hz⟩
  set N : ℕ := t.card + 1 with hNdef
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hεN : 0 < ε / N := div_pos hε hNpos
  have hfam : ∀ i : t, ∃ (n : ℕ) (l u : Fin n → ℝ), (∀ j, l j ≤ u j) ∧
      (∑ j, (u j - l j)) < ε / N ∧
      ∀ p : X, p ∈ (chartAt ℂ (i : X)).source →
        (chartAt ℂ (i : X)) p ∈ Metric.closedBall ((chartAt ℂ (i : X)) (i : X)) (r (i : X)) →
        fderiv ℝ (fun w : ℂ => g ((chartAt ℂ (i : X)).symm w)) ((chartAt ℂ (i : X)) p) = 0 →
        ∃ j, g p ∈ Set.Icc (l j) (u j) := fun i => hloc (i : X) (ε / N) hεN
  choose n l u hlu hsum hcovi using hfam
  obtain ⟨M, l', u', hlu', hsum', hcov'⟩ := exists_fin_intervals_of_sigma n l u hlu
  refine ⟨M, l', u', hlu', ?_, ?_⟩
  · have h1 : (∑ i : t, ∑ j : Fin (n i), (u i j - l i j)) < ∑ _i : t, ε / N := by
      obtain ⟨a, ha⟩ := htne
      have h := Finset.sum_lt_sum (s := Finset.univ)
        (fun i _ => le_of_lt (hsum i))
        ⟨⟨a, ha⟩, Finset.mem_univ _, hsum ⟨a, ha⟩⟩
      simpa using h
    have h2 : (∑ _i : t, ε / N) = (t.card : ℝ) * (ε / N) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
    have h3 : (t.card : ℝ) * (ε / N) < ε := by
      have hcard : (t.card : ℝ) < (N : ℝ) := by
        rw [hNdef]; push_cast; linarith
      have hlt : (t.card : ℝ) / N < 1 := (div_lt_one hNpos).mpr hcard
      calc (t.card : ℝ) * (ε / N) = ((t.card : ℝ) / N) * ε := by ring
        _ < 1 * ε := mul_lt_mul_of_pos_right hlt hε
        _ = ε := one_mul ε
    rw [hsum']
    linarith
  · intro p hpK hcrit
    obtain ⟨z, hz, hpball⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_union_left {x₀} hpK))
    have hpsrc : p ∈ (chartAt ℂ (z : X)).source := hpball.1
    have hpopen : (chartAt ℂ (z : X)) p ∈
        Metric.ball ((chartAt ℂ (z : X)) (z : X)) (r (z : X)) := hpball.2
    have hpcl : (chartAt ℂ (z : X)) p ∈
        Metric.closedBall ((chartAt ℂ (z : X)) (z : X)) (r (z : X)) :=
      Metric.ball_subset_closedBall hpopen
    have hdiffp : DifferentiableAt ℝ (fun w : ℂ => g ((chartAt ℂ p).symm w))
        ((chartAt ℂ p) p) := (contDiffAt_chartPullback hg p).differentiableAt (by decide)
    have hcritz : fderiv ℝ (fun w : ℂ => g ((chartAt ℂ (z : X)).symm w))
        ((chartAt ℂ (z : X)) p) = 0 :=
      fderiv_chartPullback_self_eq_zero hpsrc hdiffp hcrit
    obtain ⟨j, hj⟩ := hcovi ⟨z, hz⟩ p hpsrc hpcl hcritz
    exact hcov' ⟨z, hz⟩ j (g p) hj

/-! ## Existence of a regular level -/

/-- **A regular level of a smooth function exists above any level.**  For a `C^∞` function `g` on a
surface, a compact set `K` and any `C₀`, there is `C ∈ (C₀, C₀ + 1]` such that every point of `K`
with `g p = C` has non-vanishing chart derivative: `C` is not a critical value on `K`. -/
theorem exists_regular_level_of_contMDiff {g : X → ℝ}
    (hg : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ g)
    {K : Set X} (hK : IsCompact K) (x₀ : X) {C₀ : ℝ} :
    ∃ C : ℝ, C₀ < C ∧ C ≤ C₀ + 1 ∧
      ∀ p ∈ K, g p = C →
        DifferentiableAt ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ∧
        fderiv ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ≠ 0 := by
  obtain ⟨n, l, u, hlu, hsum, hcov⟩ := exists_intervals_cover_criticalValues_of_contMDiff hg
    (K := K) hK x₀ (ε := 1 / 2) (by norm_num)
  have hnot : ¬ (Set.Ioo C₀ (C₀ + 1) ⊆ ⋃ i, Set.Icc (l i) (u i)) := by
    intro hsub
    have hsub' : Set.Icc (C₀ + 1/4) (C₀ + 3/4) ⊆ ⋃ i, Set.Icc (l i) (u i) :=
      fun x hx => hsub ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hlen := Work.SimplyConnected.ABS.le_sum_length_of_Icc_subset_iUnion hlu hsub'
    have h2 : (C₀ + 3/4) - (C₀ + 1/4) = 1/2 := by ring
    linarith
  rw [Set.not_subset] at hnot
  obtain ⟨C, hC, hCnot⟩ := hnot
  refine ⟨C, hC.1, le_of_lt hC.2, ?_⟩
  intro p hpK hgp
  refine ⟨(contDiffAt_chartPullback hg p).differentiableAt (by decide), ?_⟩
  intro h0
  obtain ⟨i, hi⟩ := hcov p hpK h0
  exact hCnot (Set.mem_iUnion.mpr ⟨i, by rwa [hgp] at hi⟩)

end Work.SimplyConnected.ABS.green_reduction
