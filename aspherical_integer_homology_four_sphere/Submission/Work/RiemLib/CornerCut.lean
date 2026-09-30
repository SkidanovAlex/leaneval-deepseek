import Submission.Work.RiemLib.GlobalExp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The corner-cutting lemma

This file contains the *local no-corner* ingredient of Hopf–Rinow:

* `exists_chartGram_le_nhds`: the chart metric at points near the centre is dominated by the chart
  metric at the centre (a quantitative continuity statement for the metric tensor, needed to
  estimate the length of the coordinate-straight segment between two nearby points);
* `exists_pos_hasChartGeodesic_fibre`: chart geodesics exist for all velocities of small *fibre*
  norm (the fibre-norm form of `Geodesic.exists_pos_hasChartGeodesic`);
* `GExp_smul_isGeodesicAt`, `contMDiffOn_GExp_smul`: the curve `s ↦ GExp z (s • v)` is a smooth
  geodesic near `0` (this is the ray property in a two-sided form, obtained by comparing the two
  rays in the directions `v` and `-v` with the chosen geodesic segments);
* `GExp_smul_eq_chartRay`: the identification of that curve with the chart ray of
  `GeodesicGlobal.exists_geodesic_ray`, which gives the second-order expansion in the chart;
* **`corner_cut`**: for unit and distinct `ξ η : T_zM` and small `τ > 0`, the two points
  `GExp z (-τ • ξ)` and `GExp z (τ • η)` are at Riemannian distance `< 2τ` — equivalently, a
  minimising broken geodesic passing through `z` has no corner at `z`.

The proof of `corner_cut` produces, in the chart at `z`, the coordinate-straight segment between
the two endpoints and estimates its length using `exists_chartGram_le_nhds`; the second-order
expansion of the two chart geodesics turns that estimate into `< 2τ` because the two unit
directions `ξ`, `η` are distinct (strict convexity of the norm).
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
open Submission.Distance
open Submission.GlobalExp

namespace Submission.CornerCut

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

/-! ## The quantitative continuity of the chart metric -/

/-- **The chart metric at points near the centre is dominated by the chart metric at the centre.**
For every `c > 0` there is a neighbourhood `U` of `x₀` such that
`chartGram x₀ p a a ≤ (1 + c) * chartGram x₀ x₀ a a` for all `p ∈ U` and all `a : E`. -/
theorem exists_chartGram_le_nhds [Nontrivial E] (x₀ : M) {c : ℝ} (hc : 0 < c) :
    ∃ U : Set M, U ∈ 𝓝 x₀ ∧ ∀ p ∈ U, ∀ a : E,
      chartGram (I := I) x₀ p a a ≤ (1 + c) * chartGram (I := I) x₀ x₀ a a := by
  classical
  have hxsrc : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := exists_chartGram_bounds (I := I) x₀
    (K := ({x₀} : Set M)) isCompact_singleton ⟨x₀, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hxsrc)
  -- the unit sphere of the chart metric at the centre
  set S : Set E := {a : E | chartGram (I := I) x₀ x₀ a a = 1} with hSdef
  have hQcont : Continuous (fun a : E => chartGram (I := I) x₀ x₀ a a) := by
    obtain bb : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
    have hfun : (fun a : E => chartGram (I := I) x₀ x₀ a a)
        = fun a : E => ∑ i, ∑ j, (bb.repr a i) * (bb.repr a j) *
            chartGram (I := I) x₀ x₀ (bb i) (bb j) := by
      funext a
      exact chartGram_eq_sum_repr (I := I) bb x₀ x₀ a a
    rw [hfun]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((continuous_basis_repr bb i).mul (continuous_basis_repr bb j)).mul continuous_const
  have hSclosed : IsClosed S := isClosed_eq hQcont continuous_const
  have hSsub : S ⊆ Metric.closedBall (0 : E) (Real.sqrt (1 / lam)) := by
    intro a ha
    rw [hSdef, Set.mem_ofPred_eq] at ha
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := (hbnd x₀ (by simp) a).1
    rw [ha] at h1
    have h2 : ‖a‖ ^ 2 ≤ 1 / lam := by
      rw [le_div_iff₀ hlam]
      linarith [h1, hlam]
    rw [← Real.sqrt_sq (norm_nonneg a)]
    exact Real.sqrt_le_sqrt h2
  have hScomp : IsCompact S :=
    (isCompact_closedBall (0 : E) (Real.sqrt (1 / lam))).of_isClosed_subset hSclosed hSsub
  -- for each point of the sphere the difference of the quadratic forms is small nearby
  set F : M × E → ℝ := fun q =>
    chartGram (I := I) x₀ q.1 q.2 q.2 - chartGram (I := I) x₀ x₀ q.2 q.2 with hFdef
  have key : ∀ a : S, ∃ U : Set M, ∃ V : Set E, U ∈ 𝓝 x₀ ∧ IsOpen V ∧ (a : E) ∈ V ∧
      ∀ p ∈ U, ∀ b ∈ V, |F (p, b)| < c := by
    intro a
    have hcontG : ContinuousAt (fun q : M × E => chartGram (I := I) x₀ q.1 q.2 q.2)
        (x₀, (a : E)) := continuousAt_chartGram_prod (I := I) x₀ hxsrc (a : E)
    have hcont3 : ContinuousAt (fun b : E => chartGram (I := I) x₀ x₀ b b) ((a : E)) :=
      hcontG.comp (ContinuousAt.prodMk continuousAt_const continuousAt_id)
    have hcont2 : ContinuousAt (fun q : M × E => chartGram (I := I) x₀ x₀ q.2 q.2)
        (x₀, (a : E)) := by
      have h := hcont3.comp' (f := (Prod.snd : M × E → E)) (x := (x₀, (a : E))) continuousAt_snd
      exact h
    have hcontF : ContinuousAt F (x₀, (a : E)) := hcontG.sub hcont2
    have hF0 : F (x₀, (a : E)) = 0 := by
      simp only [hFdef]; ring
    have hmem : {q : M × E | |F q| < c} ∈ 𝓝 (x₀, (a : E)) := by
      have h1 : {q : M × E | |F q| < c} = (fun q : M × E => |F q|) ⁻¹' Iio c := rfl
      rw [h1]
      exact hcontF.abs.preimage_mem_nhds (isOpen_Iio.mem_nhds (by rw [hF0]; simpa using hc))
    have hmem' : {q : M × E | |F q| < c} ∈ 𝓝 x₀ ×ˢ 𝓝 ((a : E)) := by
      rw [← nhds_prod_eq]
      exact hmem
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hmem'
    obtain ⟨V', hV'sub, hV'open, haV'⟩ := _root_.mem_nhds_iff.mp hV
    exact ⟨U, V', hU, hV'open, haV', fun p hp b hb => hUV ⟨hp, hV'sub hb⟩⟩
  choose U V hUmem hVopen haV hUsmall using key
  -- a finite subcover of the sphere
  obtain ⟨t, ht⟩ := hScomp.elim_finite_subcover V hVopen
    (fun b hb => Set.mem_iUnion.mpr ⟨⟨b, hb⟩, haV ⟨b, hb⟩⟩)
  refine ⟨⋂ i ∈ t, U i, (Filter.biInter_finset_mem t).mpr (fun i _ => hUmem i), ?_⟩
  intro p hp a
  -- handle the zero vector separately
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [chartGram_zero, chartGram_zero, mul_zero]
  set g : ℝ := chartGram (I := I) x₀ x₀ a a with hgdef
  have hgpos : 0 < g := by rw [hgdef]; exact chartGram_self_pos hxsrc ha0
  set a₀ : E := (Real.sqrt g)⁻¹ • a with ha₀def
  have hsqrtne : Real.sqrt g ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hgpos)
  have hQa₀ : chartGram (I := I) x₀ x₀ a₀ a₀ = 1 := by
    rw [ha₀def, chartGram_smul_smul, ← hgdef, inv_pow, Real.sq_sqrt hgpos.le,
      inv_mul_cancel₀ (ne_of_gt hgpos)]
  have ha₀S : a₀ ∈ S := by rw [hSdef, Set.mem_ofPred_eq]; exact hQa₀
  have hsmall : |F (p, a₀)| < c := by
    obtain ⟨i, hi, hbi⟩ := Set.mem_iUnion₂.mp (ht ha₀S)
    exact hUsmall i p (Set.mem_iInter₂.mp hp i hi) a₀ hbi
  have hsplit : a = Real.sqrt g • a₀ := by
    rw [ha₀def, smul_smul, mul_inv_cancel₀ hsqrtne, one_smul]
  have hFsmul : F (p, a) = g * F (p, a₀) := by
    simp only [hFdef]
    rw [← hgdef]
    rw [hsplit, chartGram_smul_smul]
    have hs : Real.sqrt g ^ 2 = g := Real.sq_sqrt hgpos.le
    rw [hs, hQa₀]
    ring
  have hmain : chartGram (I := I) x₀ p a a = g * (1 + F (p, a₀)) := by
    have h1 : chartGram (I := I) x₀ p a a = g + F (p, a) := by
      simp only [hFdef]; ring
    rw [h1, hFsmul]; ring
  rw [hmain]
  have hlt : 1 + F (p, a₀) < 1 + c := by linarith [(abs_lt.mp hsmall).2]
  calc g * (1 + F (p, a₀)) ≤ g * (1 + c) := mul_le_mul_of_nonneg_left hlt.le hgpos.le
    _ = (1 + c) * chartGram (I := I) x₀ x₀ a a := by rw [hgdef]; ring

/-- **Chart geodesics exist for all velocities of small fibre norm.** -/
theorem exists_pos_hasChartGeodesic_fibre [I.Boundaryless] [Nontrivial E]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : TangentSpace I x₀, ‖v‖ ≤ ρ →
      ∃ u w : ℝ → E, HasChartGeodesic cov x₀ v u w := by
  obtain ⟨ρc, hρc, hex⟩ := exists_pos_hasChartGeodesic (cov := cov) x₀
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := exists_chartGram_bounds (I := I) x₀
    (K := ({x₀} : Set M)) isCompact_singleton ⟨x₀, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact mem_chart_source H x₀)
  have hsq : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  refine ⟨Real.sqrt lam * ρc, by positivity, fun v hv => ?_⟩
  have h1 : lam * ((fun z : E => ‖z‖) v) ^ 2
      ≤ chartGram (I := I) x₀ x₀ (v : E) (v : E) := (hbnd x₀ (by simp) (v : E)).1
  have h2 : chartGram (I := I) x₀ x₀ (v : E) (v : E) = ‖v‖ ^ 2 := by
    rw [chartGram_self_apply (I := I) x₀ (v : E) (v : E), real_inner_self_eq_norm_sq]
  have hm : ((fun z : E => ‖z‖) v) ^ 2 ≤ ρc ^ 2 := by
    have h3 : lam * ((fun z : E => ‖z‖) v) ^ 2 ≤ ‖v‖ ^ 2 := le_trans h1 (le_of_eq h2)
    have h4 : ‖v‖ ^ 2 ≤ (Real.sqrt lam * ρc) ^ 2 := by
      have h := hv
      nlinarith [norm_nonneg v, hsq.le, hρc.le]
    have h5 : (Real.sqrt lam * ρc) ^ 2 = lam * ρc ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hlam.le]
    rw [h5] at h4
    nlinarith [h3, h4, hlam]
  have hm' : (fun z : E => ‖z‖) v ≤ ρc := by
    have h := sq_le_sq.mp hm
    rw [abs_of_nonneg hρc.le] at h
    exact (abs_le.mp h).2
  exact hex v hm'


/-! ## The identification of the global exponential map with a chart ray -/

/-- **A geodesic through `z` with unit velocity `v` agrees near `0` with the global exponential
map.**  If `γ` is a smooth geodesic on `Ioo (-ε) ε` with `γ 0 = z`, `γ'(0) = v` (and non-vanishing
velocity), then `γ τ = GExp z (τ • v)` for small `τ > 0`. -/
theorem GExp_smul_eq_chartRay [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] {hmet : IsMetricCompatible cov}
    {z : M} {v : TangentSpace I z} (hv : ‖v‖ = 1) (hvne : v ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {γ : ℝ → M} (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (-ε) ε))
    (hgeo : ∀ t ∈ Ioo (-ε) ε, IsGeodesicAt cov γ t)
    (hne : ∀ t ∈ Ioo (-ε) ε, curveVelocity (I := I) γ t ≠ 0)
    (h0 : γ 0 = z) (hv0 : curveVelocity (I := I) γ 0 = v) :
    ∃ ε' : ℝ, 0 < ε' ∧ ∀ τ : ℝ, 0 < τ → τ < ε' → γ τ = GExp (cov := cov) hmet z (τ • v) := by
  obtain ⟨hgc0, hgcv, hgcsm, hgcgeo, hgcspeed⟩ :=
    geodCurve_spec (cov := cov) hmet 1 (by norm_num : (0:ℝ) ≤ 1) z v hv
  set H : ℝ → M := geodCurve (cov := cov) hmet 1 (by norm_num : (0:ℝ) ≤ 1) z v hv with hHdef
  have hδ : 0 < geodDelta (cov := cov) hmet := geodDelta_pos (cov := cov) hmet
  set ε'' : ℝ := min (min ε (geodDelta (cov := cov) hmet)) 1 / 2 with hε''def
  have hε''pos : 0 < ε'' := by
    rw [hε''def]
    have : 0 < min (min ε (geodDelta (cov := cov) hmet)) 1 := lt_min (lt_min hε hδ) one_pos
    linarith
  have hε''lt : ε'' < ε := by
    rw [hε''def]
    have h1 : min (min ε (geodDelta (cov := cov) hmet)) 1 ≤ min ε (geodDelta (cov := cov) hmet) :=
      min_le_left _ _
    have h2 : min ε (geodDelta (cov := cov) hmet) ≤ ε := min_le_left _ _
    linarith
  have hε''gd : ε'' < geodDelta (cov := cov) hmet := by
    rw [hε''def]
    have h1 : min (min ε (geodDelta (cov := cov) hmet)) 1 ≤ min ε (geodDelta (cov := cov) hmet) :=
      min_le_left _ _
    have h2 : min ε (geodDelta (cov := cov) hmet) ≤ geodDelta (cov := cov) hmet := min_le_right _ _
    linarith
  have hε''one : ε'' < 1 := by
    rw [hε''def]
    have h1 : min (min ε (geodDelta (cov := cov) hmet)) 1 ≤ 1 := min_le_right _ _
    linarith
  have hmemγ : ∀ t ∈ Ioo (-ε'') ε'', t ∈ Ioo (-ε) ε :=
    fun t ht => Set.mem_Ioo.mpr ⟨by linarith [ht.1, hε''lt], by linarith [ht.2, hε''lt]⟩
  have hmemH : ∀ t ∈ Ioo (-ε'') ε'',
      t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (1 + geodDelta (cov := cov) hmet) :=
    fun t ht => Set.mem_Ioo.mpr ⟨by linarith [ht.1, hε''gd], by linarith [ht.2, hε''one, hδ]⟩
  have hHsm : ContMDiffOn 𝓘(ℝ) I ∞ H (Ioo (-ε'') ε'') := by
    rw [hHdef]; exact hgcsm.mono hmemH
  have hHgeo : ∀ t ∈ Ioo (-ε'') ε'', IsGeodesicAt cov H t := by
    intro t ht; rw [hHdef]; exact hgcgeo t (hmemH t ht)
  have hHne : ∀ t ∈ Ioo (-ε'') ε'', curveVelocity (I := I) H t ≠ 0 := by
    intro t ht hzero
    have h1 : ‖curveVelocity (I := I) H t‖ = 1 := by
      rw [hHdef]; exact hgcspeed t (hmemH t ht)
    rw [hzero, norm_zero] at h1
    norm_num at h1
  have hH0 : H 0 = z := hgc0
  have hHv : curveVelocity (I := I) H 0 = v := hgcv
  have heq : EqOn γ H (Ioo (-ε'') ε'') :=
    eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) (hsm.mono hmemγ) hHsm
      (fun t ht => hgeo t (hmemγ t ht)) hHgeo (fun t ht => hne t (hmemγ t ht)) hHne
      (Set.mem_Ioo.mpr ⟨by linarith [hε''pos], hε''pos⟩) (by rw [h0, hH0]) (by rw [hv0, hHv])
  refine ⟨ε'', hε''pos, fun τ hτ hτ' => ?_⟩
  have hτne : τ • v ≠ 0 := smul_ne_zero (ne_of_gt hτ) hvne
  have hnorm : ‖τ • v‖ = τ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ, hv, mul_one]
  have hunit : unitOf (τ • v) hτne = v := by
    rw [unitOf, hnorm, smul_smul, inv_mul_cancel₀ (ne_of_gt hτ), one_smul]
  have hτone : τ < 1 := by linarith [hτ', hε''one]
  have h1 : GExp (cov := cov) hmet z (τ • v)
      = (geodCurve (cov := cov) hmet ‖τ • v‖ (norm_nonneg _) z (unitOf (τ • v) hτne)
          (unitOf_norm (τ • v) hτne)) ‖τ • v‖ :=
    GExp_apply (cov := cov) hmet hτne
  have h2 : (geodCurve (cov := cov) hmet ‖τ • v‖ (norm_nonneg _) z (unitOf (τ • v) hτne)
        (unitOf_norm (τ • v) hτne)) ‖τ • v‖ = H τ := by
    have hstep1 : (geodCurve (cov := cov) hmet ‖τ • v‖ (norm_nonneg _) z (unitOf (τ • v) hτne)
          (unitOf_norm (τ • v) hτne)) ‖τ • v‖
        = (geodCurve (cov := cov) hmet ‖τ • v‖ (norm_nonneg _) z v hv) ‖τ • v‖ :=
      geodCurve_agree_of_eq (cov := cov) hmet (x := z) hunit (unitOf_norm (τ • v) hτne) hv
        (T₁ := ‖τ • v‖) (T₂ := ‖τ • v‖) (norm_nonneg (τ • v)) (norm_nonneg (τ • v)) le_rfl
        (Set.mem_Ioo.mpr ⟨by linarith [hδ, norm_nonneg (τ • v)], by linarith [hδ]⟩)
    have hstep2 : (geodCurve (cov := cov) hmet ‖τ • v‖ (norm_nonneg _) z v hv) ‖τ • v‖
        = (geodCurve (cov := cov) hmet 1 (by norm_num : (0:ℝ) ≤ 1) z v hv) ‖τ • v‖ :=
      geodCurve_agree (cov := cov) (T₁ := ‖τ • v‖) (T₂ := 1) hmet (norm_nonneg (τ • v))
        (by norm_num : (0:ℝ) ≤ 1) (le_of_lt (by rw [hnorm]; exact hτone)) z v hv
        (Set.mem_Ioo.mpr ⟨by linarith [hδ, norm_nonneg (τ • v)], by linarith [hδ]⟩)
    rw [hstep1, hstep2, hHdef]
    exact congrArg (geodCurve (cov := cov) hmet 1 (by norm_num : (0:ℝ) ≤ 1) z v hv) hnorm
  rw [h1, h2]
  exact heq (Set.mem_Ioo.mpr ⟨by linarith [hτ, hε''pos], hτ'⟩)


/-! ## Two elementary tools -/

/-- **The first-order expansion of a differentiable curve.**  If `f` has derivative `f'` at `0`, then
`‖f s - f 0 - s • f'‖ < e |s|` for `s` close to (and different from) `0`. -/
lemma exists_norm_sub_le_of_hasDerivAt {f : ℝ → E} {f' : E} {e : ℝ} (he : 0 < e)
    (h : HasDerivAt f f' 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, s ≠ 0 → |s| < δ → ‖f s - f 0 - s • f'‖ < e * |s| := by
  have hmem : {s : ℝ | dist (‖s - 0‖⁻¹ * ‖f s - f 0 - (s - 0) • f'‖) 0 < e} ∈ 𝓝 (0 : ℝ) :=
    (hasDerivAt_iff_tendsto.mp h).eventually (Metric.ball_mem_nhds 0 he)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨r, hr, fun s hsne hsr => ?_⟩
  have hs : s ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hsr
  have h3 : dist (‖s - 0‖⁻¹ * ‖f s - f 0 - (s - 0) • f'‖) 0 < e := hsub hs
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖s - 0‖⁻¹ *
    ‖f s - f 0 - (s - 0) • f'‖)] at h3
  simp only [sub_zero] at h3
  have hpos : 0 < |s| := abs_pos.mpr hsne
  calc ‖f s - f 0 - s • f'‖
      = |s| * (‖s‖⁻¹ * ‖f s - f 0 - s • f'‖) := by
        rw [Real.norm_eq_abs, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
    _ < |s| * e := mul_lt_mul_of_pos_left h3 hpos
    _ = e * |s| := by ring

/-- The frame vector of the coordinates of a tangent vector is that tangent vector. -/
lemma frameVector_continuousLinearMapAt (z : M) (v : TangentSpace I z) :
    frameVector (I := I) z z
      ((trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ z v) = v :=
  Trivialization.symmL_continuousLinearMapAt (R := ℝ) (b := z)
    (e := trivializationAt E (TangentSpace I) z) (by simp) v


/-! ## The data of a unit chart ray -/

/-- **The data attached to a unit chart ray.**  For a unit tangent vector `v` at `z` and a chart
geodesic existence radius `ρ`, there are `ε > 0` (with `ε ≤ ρ`) and a chart solution `(u,w)` of the
geodesic equation such that, on `(0, ε)`, the curve `s ↦ (extChartAt I z).symm (u s)` agrees with
`s ↦ GExp z (s • v)`, and `u` has the second-order expansion
`‖u s - u 0 - s • (w 0)‖ < e |s|` at the origin. -/
lemma chartRay_data [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] {hmet : IsMetricCompatible cov}
    {z : M} {v : TangentSpace I z} (hv : ‖v‖ = 1) (hvne : v ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hex : ∀ w : TangentSpace I z, ‖w‖ ≤ ρ → ∃ u w' : ℝ → E, HasChartGeodesic cov z w u w')
    {e : ℝ} (he : 0 < e) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ρ ∧ ∃ u w : ℝ → E,
      u 0 = (extChartAt I z) z ∧
      w 0 = (trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ z v ∧
      (∀ s ∈ Ioo (0 : ℝ) ε, (extChartAt I z).symm (u s) = GExp (cov := cov) hmet z (s • v)) ∧
      (∀ s : ℝ, s ≠ 0 → |s| < ε → ‖u s - u 0 - s • (w 0)‖ < e * |s|) := by
  classical
  obtain ⟨u₀, w₀, h₀, hw₀, htgt, hd, hw', hsp, hgeo, hsm⟩ :=
    Submission.GeodesicGlobal.exists_geodesic_ray (cov := cov) z hρ hex hmet v hvne
  simp only [hv, div_one] at htgt hd hw' hsp hgeo hsm
  have h0mem : (0 : ℝ) ∈ Ioo (-(2 * ρ)) (2 * ρ) := ⟨by linarith [hρ], by linarith [hρ]⟩
  have hα0 : (fun s : ℝ => (extChartAt I z).symm (u₀ s)) 0 = z := by
    show (extChartAt I z).symm (u₀ 0) = z
    rw [h₀]
    exact (extChartAt I z).left_inv (mem_extChartAt_source z)
  have hαv : curveVelocity (I := I) (fun s : ℝ => (extChartAt I z).symm (u₀ s)) 0 = v := by
    have htgt0 : u₀ 0 ∈ (extChartAt I z).target := htgt 0 h0mem
    have hstay : ∀ᶠ s in 𝓝 (0 : ℝ), u₀ s ∈ (extChartAt I z).target := by
      filter_upwards [isOpen_Ioo.mem_nhds h0mem] with s hs
      exact htgt s hs
    have h := curveVelocity_extChartAt_symm (I := I) (x₀ := z) (u := u₀) (t := 0)
      (v := w₀ 0) (hd 0 h0mem) htgt0 hstay
    rw [h, hw₀, h₀, (extChartAt I z).left_inv (mem_extChartAt_source z)]
    exact frameVector_continuousLinearMapAt z v
  have hαne : ∀ t ∈ Ioo (-ρ) ρ,
      curveVelocity (I := I) (fun s : ℝ => (extChartAt I z).symm (u₀ s)) t ≠ 0 := by
    intro t ht hzero
    have h1 := hsp t ⟨by linarith [ht.1, hρ], by linarith [ht.2, hρ]⟩
    rw [hzero, norm_zero] at h1
    norm_num at h1
  obtain ⟨ε₁, hε₁, hG⟩ := GExp_smul_eq_chartRay (cov := cov) (z := z) hv hvne (ε := ρ) hρ
    (γ := fun s : ℝ => (extChartAt I z).symm (u₀ s))
    (hsm.mono (fun t ht => ⟨by linarith [ht.1, hρ], by linarith [ht.2, hρ]⟩))
    (fun t ht => hgeo t ⟨ht.1.le, ht.2.le⟩)
    hαne hα0 hαv
  obtain ⟨δ, hδ, hδb⟩ := exists_norm_sub_le_of_hasDerivAt (f := u₀) (f' := w₀ 0) he (hd 0 h0mem)
  refine ⟨min (min ε₁ δ) ρ, lt_min (lt_min hε₁ hδ) hρ, min_le_right _ _, u₀, w₀, h₀, hw₀, ?_, ?_⟩
  · intro s hs
    exact hG s hs.1 (lt_of_lt_of_le hs.2 (le_trans (min_le_left _ _) (min_le_left _ _)))
  · intro s hsne hs
    exact hδb s hsne (lt_of_lt_of_le hs (le_trans (min_le_left _ _) (min_le_right _ _)))

/-! ## The corner-cutting lemma -/

/-- **Corner cutting.**  For distinct unit tangent vectors `ξ ≠ η` at `z`, and for all sufficiently
small `τ > 0`, the two points `GExp z (-τ • ξ)` and `GExp z (τ • η)` are at Riemannian distance
strictly less than `2τ`.  Equivalently: a minimising broken geodesic through `z` has no corner. -/
theorem corner_cut [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov) (z : M)
    {ξ η : TangentSpace I z} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hne : ξ ≠ η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℝ, 0 < τ → τ < δ →
      Manifold.riemannianEDist I (GExp hmet z ((-τ) • ξ)) (GExp hmet z (τ • η))
        < ENNReal.ofReal (2 * τ) := by
  classical
  haveI hcont : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hξne : ξ ≠ 0 := fun h => by rw [h, norm_zero] at hξ; norm_num at hξ
  have hηne : η ≠ 0 := fun h => by rw [h, norm_zero] at hη; norm_num at hη
  have hgle : ‖ξ + η‖ ≤ 2 := by
    have h := norm_add_le ξ η
    rw [hξ, hη] at h
    linarith
  have hgap : 0 < 2 - ‖ξ + η‖ := by
    rcases lt_or_eq_of_le hgle with hlt | heq
    · linarith
    · exfalso
      have h' : ‖ξ + η‖ = ‖ξ‖ + ‖η‖ := by rw [hξ, hη, heq]; norm_num
      have h2 : ‖η‖ • ξ = ‖ξ‖ • η := norm_add_eq_iff_real.mp h'
      rw [hη, hξ, one_smul, one_smul] at h2
      exact hne h2
  -- radii and chart bounds
  obtain ⟨ρc, hρc, hexc⟩ := exists_pos_hasChartGeodesic_fibre (cov := cov) z
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := exists_chartGram_bounds (I := I) z
    (K := ({z} : Set M)) isCompact_singleton ⟨z, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact mem_chart_source H z)
  have hLamp : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hLam
  have hgd : 0 < geodDelta (cov := cov) hmet := geodDelta_pos (cov := cov) hmet
  -- the constants
  set g : ℝ := 2 - ‖ξ + η‖ with hgdef
  have hgpos : 0 < g := by rw [hgdef]; exact hgap
  have hgle2 : g ≤ 2 := by
    rw [hgdef]; linarith [norm_nonneg (ξ + η)]
  have hgm : 0 < 2 - 3 * g / 4 := by linarith [hgpos, hgle2]
  set m : ℝ := 2 / (2 - 3 * g / 4) with hmdef
  have hm1 : 1 < m := by
    rw [hmdef, lt_div_iff₀ hgm]
    linarith [hgpos]
  set cc : ℝ := (m ^ 2 - 1) / 2 with hccdef
  have hccpos : 0 < cc := by rw [hccdef]; nlinarith [hm1]
  have hsqrtcc : Real.sqrt (1 + cc) < m := by
    rw [Real.sqrt_lt' (by linarith : (0:ℝ) < m), hccdef]
    nlinarith [hm1]
  have hkey : Real.sqrt (1 + cc) * (2 - 3 * g / 4) < 2 := by
    calc Real.sqrt (1 + cc) * (2 - 3 * g / 4) < m * (2 - 3 * g / 4) :=
          mul_lt_mul_of_pos_right hsqrtcc hgm
      _ = 2 := by rw [hmdef]; exact div_mul_cancel₀ 2 (ne_of_gt hgm)
  -- the expansion tolerance
  set ee : ℝ := g / (8 * Real.sqrt Lam) with heedef
  have heepos : 0 < ee := by rw [heedef]; positivity
  have heeL : ee * Real.sqrt Lam = g / 8 := by
    rw [heedef]; field_simp
  -- the two chart rays
  obtain ⟨ε₁, hε₁pos, hε₁ρ, u₁, w₁, h₁0, h₁w, hG₁, hexp₁⟩ :=
    chartRay_data (cov := cov) (hmet := hmet) (z := z) (v := -ξ) (by rw [norm_neg]; exact hξ)
      (neg_ne_zero.mpr hξne) (ρ := ρc) hρc hexc heepos
  obtain ⟨ε₂, hε₂pos, hε₂ρ, u₂, w₂, h₂0, h₂w, hG₂, hexp₂⟩ :=
    chartRay_data (cov := cov) (hmet := hmet) (z := z) (v := η) hη hηne
      (ρ := ρc) hρc hexc heepos
  -- the coordinate velocities
  set a : E := (trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ z ξ with hadef
  set b : E := (trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ z η with hbdef
  have hw₁ : w₁ 0 = -a := by rw [h₁w, hadef, map_neg]
  have hw₂ : w₂ 0 = b := by rw [h₂w, hbdef]
  -- the metric comparison
  obtain ⟨U, hU, hUle⟩ := exists_chartGram_le_nhds (I := I) z (c := cc) hccpos
  have htgtmem : (extChartAt I z).target ∈ 𝓝 ((extChartAt I z) z) :=
    (isOpen_extChartAt_target z).mem_nhds ((extChartAt I z).map_source (mem_extChartAt_source z))
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.mem_nhds_iff.mp htgtmem
  have hUpre : (extChartAt I z).symm ⁻¹' U ∈ 𝓝 ((extChartAt I z) z) :=
    (continuousAt_extChartAt_symm (I := I) z).preimage_mem_nhds (by
      rw [show (extChartAt I z).symm ((extChartAt I z) z) = z from
        (extChartAt I z).left_inv (mem_extChartAt_source z)]
      exact hU)
  obtain ⟨r₂, hr₂, hr₂sub⟩ := Metric.mem_nhds_iff.mp hUpre
  set r : ℝ := min r₁ r₂ with hrdef
  have hrpos : 0 < r := lt_min hr₁ hr₂
  have hrmem : ∀ x : E, x ∈ Metric.ball ((extChartAt I z) z) r →
      x ∈ (extChartAt I z).target ∧ (extChartAt I z).symm x ∈ U := by
    intro x hx
    have hx₁ : x ∈ Metric.ball ((extChartAt I z) z) r₁ :=
      Metric.ball_subset_ball (min_le_left _ _) hx
    have hx₂ : x ∈ Metric.ball ((extChartAt I z) z) r₂ :=
      Metric.ball_subset_ball (min_le_right _ _) hx
    exact ⟨hr₁sub hx₁, hr₂sub hx₂⟩
  set Ma : ℝ := ‖a‖ + ee with hMadef
  set Mb : ℝ := ‖b‖ + ee with hMbdef
  refine ⟨min (min ε₁ ε₂) (min (r / Ma) (r / Mb)), ?_, fun τ hτ hτδ => ?_⟩
  · have h1 : 0 < Ma := by rw [hMadef]; positivity
    have h2 : 0 < Mb := by rw [hMbdef]; positivity
    exact lt_min (lt_min hε₁pos hε₂pos) (lt_min (div_pos hrpos h1) (div_pos hrpos h2))
  -- the main argument
  have hτε₁ : τ < ε₁ := lt_of_lt_of_le hτδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hτε₂ : τ < ε₂ := lt_of_lt_of_le hτδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hτMa : τ < r / Ma := lt_of_lt_of_le hτδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hτMb : τ < r / Mb := lt_of_lt_of_le hτδ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hMapos : 0 < Ma := by rw [hMadef]; positivity
  have hMbpos : 0 < Mb := by rw [hMbdef]; positivity
  -- the endpoints
  have hP0 : (extChartAt I z).symm (u₁ τ) = GExp hmet z ((-τ) • ξ) := by
    rw [hG₁ τ (Set.mem_Ioo.mpr ⟨hτ, hτε₁⟩), smul_neg, neg_smul]
  have hP1 : (extChartAt I z).symm (u₂ τ) = GExp hmet z (τ • η) :=
    hG₂ τ (Set.mem_Ioo.mpr ⟨hτ, hτε₂⟩)
  -- the second-order expansions
  have h₁exp : ‖u₁ τ - (extChartAt I z) z + τ • a‖ < ee * τ := by
    have h := hexp₁ τ (ne_of_gt hτ) (by rw [abs_of_pos hτ]; exact hτε₁)
    rw [h₁0, hw₁, abs_of_pos hτ] at h
    have heq : u₁ τ - (extChartAt I z) z - τ • (-a) = u₁ τ - (extChartAt I z) z + τ • a := by
      rw [smul_neg, sub_neg_eq_add]
    rwa [heq] at h
  have h₂exp : ‖u₂ τ - (extChartAt I z) z - τ • b‖ < ee * τ := by
    have h := hexp₂ τ (ne_of_gt hτ) (by rw [abs_of_pos hτ]; exact hτε₂)
    rwa [h₂0, hw₂, abs_of_pos hτ] at h
  -- the coordinate difference
  set Δ : E := u₂ τ - u₁ τ with hΔdef
  have herr : ‖Δ - τ • (a + b)‖ < 2 * ee * τ := by
    have hsplit : Δ - τ • (a + b)
        = (u₂ τ - (extChartAt I z) z - τ • b) - (u₁ τ - (extChartAt I z) z + τ • a) := by
      rw [hΔdef]; module
    have h3 : ‖Δ - τ • (a + b)‖ ≤ ‖u₂ τ - (extChartAt I z) z - τ • b‖
        + ‖u₁ τ - (extChartAt I z) z + τ • a‖ := by
      rw [hsplit]; exact norm_sub_le _ _
    linarith [h₁exp, h₂exp]
  -- the two endpoints lie in the small ball
  have h₁le : ‖u₁ τ - (extChartAt I z) z‖ < τ * Ma := by
    have h2 : ‖u₁ τ - (extChartAt I z) z‖
        ≤ ‖u₁ τ - (extChartAt I z) z + τ • a‖ + ‖τ • a‖ := by
      have heq : u₁ τ - (extChartAt I z) z
          = (u₁ τ - (extChartAt I z) z + τ • a) - τ • a := by abel
      conv_lhs => rw [heq]
      exact norm_sub_le _ _
    have h3 : ‖τ • a‖ = τ * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
    rw [h3] at h2
    rw [hMadef]
    linarith [h₁exp, h2]
  have h₂le : ‖u₂ τ - (extChartAt I z) z‖ < τ * Mb := by
    have h2 : ‖u₂ τ - (extChartAt I z) z‖
        ≤ ‖u₂ τ - (extChartAt I z) z - τ • b‖ + ‖τ • b‖ := by
      have heq : u₂ τ - (extChartAt I z) z
          = (u₂ τ - (extChartAt I z) z - τ • b) + τ • b := by abel
      conv_lhs => rw [heq]
      exact norm_add_le _ _
    have h3 : ‖τ • b‖ = τ * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
    rw [h3] at h2
    rw [hMbdef]
    linarith [h₂exp, h2]
  have h₁dist : ‖u₁ τ - (extChartAt I z) z‖ < r := by
    have h := mul_lt_mul_of_pos_right hτMa hMapos  -- hmm
    rw [div_mul_cancel₀ _ (ne_of_gt hMapos)] at h
    linarith [h₁le]
  have h₂dist : ‖u₂ τ - (extChartAt I z) z‖ < r := by
    have h := mul_lt_mul_of_pos_right hτMb hMbpos
    rw [div_mul_cancel₀ _ (ne_of_gt hMbpos)] at h
    linarith [h₂le]
  -- the straight segment
  have hball : ∀ l ∈ Icc (0:ℝ) 1, u₁ τ + l • Δ ∈ Metric.ball ((extChartAt I z) z) r := by
    intro l hl
    rw [Metric.mem_ball, dist_eq_norm]
    have hconv : u₁ τ + l • Δ - (extChartAt I z) z
        = (1 - l) • (u₁ τ - (extChartAt I z) z) + l • (u₂ τ - (extChartAt I z) z) := by
      rw [hΔdef]; module
    rw [hconv]
    have h1l : 0 ≤ 1 - l := by linarith [hl.2]
    calc ‖(1 - l) • (u₁ τ - (extChartAt I z) z) + l • (u₂ τ - (extChartAt I z) z)‖
        ≤ ‖(1 - l) • (u₁ τ - (extChartAt I z) z)‖
            + ‖l • (u₂ τ - (extChartAt I z) z)‖ := norm_add_le _ _
      _ = (1 - l) * ‖u₁ τ - (extChartAt I z) z‖ + l * ‖u₂ τ - (extChartAt I z) z‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1l, abs_of_nonneg hl.1]
      _ < (1 - l) * r + l * r := by
          rcases eq_or_lt_of_le hl.1 with hl0 | hlpos
          · rw [← hl0]; simpa using mul_lt_mul_of_pos_left h₁dist one_pos
          rcases eq_or_lt_of_le hl.2 with hl1 | hllt
          · rw [hl1]; simpa using mul_lt_mul_of_pos_left h₂dist one_pos
          · exact add_lt_add (mul_lt_mul_of_pos_left h₁dist (by linarith : (0:ℝ) < 1 - l))
              (mul_lt_mul_of_pos_left h₂dist hlpos)
      _ = r := by ring
  -- the curve and its length
  set P : ℝ → M := fun l => (extChartAt I z).symm (u₁ τ + l • Δ) with hPdef
  have haff : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun l : ℝ => u₁ τ + l • Δ) (Icc (0:ℝ) 1) := by
    have h1 : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun l : ℝ => l • Δ) (Icc (0:ℝ) 1) :=
      contMDiffOn_id.smul contMDiffOn_const
    exact contMDiffOn_const.add h1
  have hPsmInf : ContMDiffOn 𝓘(ℝ) I ∞ P (Icc (0:ℝ) 1) := by
    rw [hPdef]
    refine (contMDiffOn_extChartAt_symm (I := I) z).comp haff (fun l hl => ?_)
    exact (hrmem _ (hball l hl)).1
  have hPsm : CMDiff[Icc (0:ℝ) 1] 1 P := hPsmInf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hP0' : P 0 = GExp hmet z ((-τ) • ξ) := by
    rw [hPdef]
    show (extChartAt I z).symm (u₁ τ + (0:ℝ) • Δ) = _
    rw [zero_smul, add_zero]
    exact hP0
  have hP1' : P 1 = GExp hmet z (τ • η) := by
    rw [hPdef]
    show (extChartAt I z).symm (u₁ τ + (1:ℝ) • Δ) = _
    have h1 : u₁ τ + (1:ℝ) • Δ = u₂ τ := by rw [hΔdef]; module
    rw [h1]
    exact hP1
  -- the pointwise speed bound
  have hspeed : ∀ l ∈ Icc (0:ℝ) 1,
      ‖(mfderiv% P l) 1‖ₑ ≤ ENNReal.ofReal (Real.sqrt (1 + cc) * Real.sqrt (chartGram (I := I) z z Δ Δ)) := by
    intro l hl
    have hx := hball l hl
    have hxtgt : u₁ τ + l • Δ ∈ (extChartAt I z).target := (hrmem _ hx).1
    have hxU : (extChartAt I z).symm (u₁ τ + l • Δ) ∈ U := (hrmem _ hx).2
    have hderiv : HasDerivAt (fun LL : ℝ => u₁ τ + LL • Δ) Δ l := by
      have h1 : HasDerivAt (fun LL : ℝ => LL • Δ) Δ l := by
        simpa using (hasDerivAt_id l).smul_const Δ
      simpa using h1.const_add (u₁ τ)
    have hstay : ∀ᶠ s in 𝓝 l, u₁ τ + s • Δ ∈ (extChartAt I z).target :=
      ((continuousAt_const.add (continuousAt_id.smul continuousAt_const)).preimage_mem_nhds
        ((isOpen_extChartAt_target z).mem_nhds hxtgt))
    have hcv : curveVelocity (I := I) P l
        = frameVector (I := I) z (P l) Δ := by
      rw [hPdef]
      exact curveVelocity_extChartAt_symm (I := I) hderiv hxtgt hstay
    have hnorm : ‖curveVelocity (I := I) P l‖ = Real.sqrt (chartGram (I := I) z (P l) Δ Δ) := by
      rw [hcv, chartGram_apply, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    have hle : chartGram (I := I) z (P l) Δ Δ ≤ (1 + cc) * chartGram (I := I) z z Δ Δ :=
      hUle _ hxU Δ
    have hstep : ‖curveVelocity (I := I) P l‖
        ≤ Real.sqrt (1 + cc) * Real.sqrt (chartGram (I := I) z z Δ Δ) := by
      rw [hnorm]
      calc Real.sqrt (chartGram (I := I) z (P l) Δ Δ)
          ≤ Real.sqrt ((1 + cc) * chartGram (I := I) z z Δ Δ) := Real.sqrt_le_sqrt hle
        _ = Real.sqrt (1 + cc) * Real.sqrt (chartGram (I := I) z z Δ Δ) :=
            Real.sqrt_mul (by linarith) _
    have h1 : ‖(mfderiv% P l) 1‖ₑ = ENNReal.ofReal ‖curveVelocity (I := I) P l‖ := by
      rw [show ‖(mfderiv% P l) 1‖ₑ = ‖curveVelocity (I := I) P l‖ₑ from rfl,
        Submission.Minimal.enorm_eq_ofReal_norm]
    rw [h1]
    exact ENNReal.ofReal_le_ofReal hstep
  -- the length bound
  have hlen : Manifold.pathELength I P 0 1
      ≤ ENNReal.ofReal (Real.sqrt (1 + cc) * Real.sqrt (chartGram (I := I) z z Δ Δ)) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have h1 : (∫⁻ (t : ℝ) in Icc (0:ℝ) 1, ‖(mfderiv% P t) 1‖ₑ)
        ≤ ∫⁻ (_ : ℝ) in Icc (0:ℝ) 1,
            ENNReal.ofReal (Real.sqrt (1 + cc) * Real.sqrt (chartGram (I := I) z z Δ Δ)) := by
      exact MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun t ht => hspeed t ht)
    refine le_trans h1 (le_of_eq ?_)
    rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
    norm_num
  -- the bound on the coordinate difference
  have hΔbound : ‖frameVector (I := I) z z Δ‖ < τ * (2 - 3 * g / 4) := by
    have hframe : frameVector (I := I) z z Δ
        = τ • (frameVector (I := I) z z a + frameVector (I := I) z z b)
          + frameVector (I := I) z z (Δ - τ • (a + b)) := by
      have h1 : frameVector (I := I) z z Δ
          = frameVector (I := I) z z (τ • (a + b)) + frameVector (I := I) z z (Δ - τ • (a + b)) := by
        rw [← frameVector_add, add_sub_cancel]
      rw [h1, frameVector_smul, frameVector_add]
    have hfa : frameVector (I := I) z z a = ξ := by
      rw [hadef]; exact frameVector_continuousLinearMapAt z ξ
    have hfb : frameVector (I := I) z z b = η := by
      rw [hbdef]; exact frameVector_continuousLinearMapAt z η
    have herrn : ‖frameVector (I := I) z z (Δ - τ • (a + b))‖ ≤ Real.sqrt Lam * ‖Δ - τ • (a + b)‖ := by
      have h2 : ‖frameVector (I := I) z z (Δ - τ • (a + b))‖
          = Real.sqrt (chartGram (I := I) z z (Δ - τ • (a + b)) (Δ - τ • (a + b))) := by
        rw [chartGram_apply, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      rw [h2]
      calc Real.sqrt (chartGram (I := I) z z (Δ - τ • (a + b)) (Δ - τ • (a + b)))
          ≤ Real.sqrt (Lam * ‖Δ - τ • (a + b)‖ ^ 2) :=
            Real.sqrt_le_sqrt ((hbnd z (by simp) _).2)
        _ = Real.sqrt Lam * ‖Δ - τ • (a + b)‖ := by
            rw [Real.sqrt_mul hLam.le, Real.sqrt_sq (norm_nonneg _)]
    rw [hframe]
    calc ‖τ • (frameVector (I := I) z z a + frameVector (I := I) z z b)
            + frameVector (I := I) z z (Δ - τ • (a + b))‖
        ≤ ‖τ • (frameVector (I := I) z z a + frameVector (I := I) z z b)‖
            + ‖frameVector (I := I) z z (Δ - τ • (a + b))‖ := norm_add_le _ _
      _ = τ * ‖ξ + η‖ + ‖frameVector (I := I) z z (Δ - τ • (a + b))‖ := by
          rw [hfa, hfb, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
      _ < τ * ‖ξ + η‖ + Real.sqrt Lam * (2 * ee * τ) := by
          have h3 : Real.sqrt Lam * ‖Δ - τ • (a + b)‖ < Real.sqrt Lam * (2 * ee * τ) :=
            mul_lt_mul_of_pos_left herr hLamp
          linarith [h3, herrn]
      _ = τ * (2 - 3 * g / 4) := by
          have h2 : Real.sqrt Lam * (2 * ee * τ) = (g / 4) * τ := by
            have h5 : Real.sqrt Lam * ee = g / 8 := by rw [mul_comm]; exact heeL
            calc Real.sqrt Lam * (2 * ee * τ) = 2 * (Real.sqrt Lam * ee) * τ := by ring
              _ = 2 * (g / 8) * τ := by rw [h5]
              _ = (g / 4) * τ := by ring
          rw [h2, hgdef]; ring
  -- conclude
  have hstep : Real.sqrt (1 + cc) * Real.sqrt (chartGram (I := I) z z Δ Δ) < 2 * τ := by
      have h1 : Real.sqrt (chartGram (I := I) z z Δ Δ) = ‖frameVector (I := I) z z Δ‖ := by
        rw [chartGram_apply, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      rw [h1]
      calc Real.sqrt (1 + cc) * ‖frameVector (I := I) z z Δ‖
          < Real.sqrt (1 + cc) * (τ * (2 - 3 * g / 4)) :=
            mul_lt_mul_of_pos_left hΔbound (Real.sqrt_pos.mpr (by linarith))
        _ = τ * (Real.sqrt (1 + cc) * (2 - 3 * g / 4)) := by ring
        _ < τ * 2 := mul_lt_mul_of_pos_left hkey hτ
        _ = 2 * τ := by ring
  have hbound : ENNReal.ofReal (Real.sqrt (1 + cc) * Real.sqrt (chartGram (I := I) z z Δ Δ))
      < ENNReal.ofReal (2 * τ) := ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mpr hstep
  have hfinal : Manifold.riemannianEDist I (P 0) (P 1) < ENNReal.ofReal (2 * τ) :=
    calc Manifold.riemannianEDist I (P 0) (P 1)
        ≤ Manifold.pathELength I P 0 1 :=
          Manifold.riemannianEDist_le_pathELength (I := I) hPsm rfl rfl zero_le_one
      _ ≤ ENNReal.ofReal (Real.sqrt (1 + cc) * Real.sqrt (chartGram (I := I) z z Δ Δ)) := hlen
      _ < ENNReal.ofReal (2 * τ) := hbound
  rwa [hP0', hP1'] at hfinal

end

end Submission.CornerCut
