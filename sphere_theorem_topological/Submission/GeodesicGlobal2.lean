import Submission.GeodesicGlobal
import Submission.ChartBounds
import Submission.Commons.Analysis.ODE.exists_uniform_secondOrderODE_solution_nhds

/-!
# The uniform restart radius, and geodesic segments of prescribed length

`Submission/GeodesicGlobal.lean` shows how to extend a geodesic across a chart, given a chart
solution with the right initial data.  This file supplies the *uniform* input that the extension
step consumes:

* `chartGram_const_of_chartODE`: the Riemannian speed of a solution of the chart geodesic equation
  on an arbitrary interval is constant (a general-interval version of
  `GeodesicSpeed.hasChartGeodesic_chartGram_const`);

* `exists_local_geodesic_neighbourhood`: **uniform local existence** of unit-speed geodesic
  segments with prescribed initial data.  For every point `x₀` there are `ρ > 0` and an open
  neighbourhood `W ∋ x₀` in the chart at `x₀` such that for *every* `y ∈ W` and every *unit*
  `ξ ∈ T_yM` there is a geodesic `γ` defined on `Ioo (-(2ρ)) (2ρ)` with `γ 0 = y`,
  `γ'(0) = ξ`, of constant speed `1`, `C^∞` on the interval and geodesic at every point of it.
  The proof combines the uniform ODE existence for the extended spray
  (`Commons.Analysis.ODE.exists_uniform_secondOrderODE_solution_nhds`) with the comparison of the
  chart metric with the model norm on a compact chart ball
  (`ChartBounds.exists_chartGram_bounds`): if `ξ` has length `1` and `a` are its coordinates in the
  frame at `y`, then `λ ‖a‖² ≤ 1`, so the coordinate velocity `(ρ₀/‖a‖) • a` has norm `ρ₀` and the
  corresponding chart geodesic has intrinsic speed `ρ₀/‖a‖ ≥ ρ₀√λ` — rescaling time by this
  factor gives a unit-speed geodesic and a uniform time interval.

* `exists_uniform_geodesic_segment`: the same statement with `ρ` **uniform over the compact
  manifold** (a finite chart cover and a minimum over a finite set of radii).
-/

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartBounds

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GeodesicGlobal2

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## The speed of a solution of the chart equation is constant -/

/-- **The squared speed of a solution of the chart geodesic equation is constant.**  This is
`GeodesicSpeed.hasChartGeodesic_chartGram_const` for an arbitrary interval `Ioo A B` and an
arbitrary reference time `t₀ ∈ Ioo A B`. -/
theorem chartGram_const_of_chartODE
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [I.Boundaryless]
    (hmet : IsMetricCompatible cov) {x₀ : M} {u w : ℝ → E} {A B : ℝ}
    (hstay : ∀ s ∈ Ioo A B, u s ∈ (extChartAt I x₀).target)
    (hu : ∀ s ∈ Ioo A B, HasDerivAt u (w s) s)
    (hw : ∀ s ∈ Ioo A B, HasDerivAt w (chartGeodesicVectorField cov x₀ (u s, w s)) s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo A B) :
    ∀ s ∈ Ioo A B,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (w s) (w s)
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (w t₀) := by
  have hderiv_zero : ∀ t ∈ Ioo A B,
      HasDerivAt (fun r : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
        (w r) (w r)) 0 t := by
    intro t ht
    have hstay' : ∀ᶠ s' in 𝓝 t, u s' ∈ (extChartAt I x₀).target :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) hstay
    have hG : chartGeodesicVectorField cov x₀ (u t, w t)
        = -christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (w t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)) := rfl
    have hmain := hasDerivAt_chartGram_curve (cov := cov) hmet x₀
      (u := u) (v := w t) (t := t) (hu t ht) (hstay t ht) hstay'
      (h₁ := w) (h₂ := w) (h₁' := chartGeodesicVectorField cov x₀ (u t, w t))
      (h₂' := chartGeodesicVectorField cov x₀ (u t, w t))
      (hw t ht) (hw t ht)
    convert hmain using 1
    rw [hG, neg_add_cancel]
    rw [Submission.Gauss.chartGram_zero_snd, Submission.Gauss.chartGram_zero_fst, add_zero]
  intro s hs
  rcases le_total t₀ s with hle | hle
  · exact Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc hle
      (fun x hx => hderiv_zero x ⟨lt_of_lt_of_le ht₀.1 hx.1, lt_of_le_of_lt hx.2 hs.2⟩)
      s ⟨hle, le_rfl⟩
  · exact (Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc hle
      (fun x hx => hderiv_zero x ⟨lt_of_lt_of_le hs.1 hx.1, lt_of_le_of_lt hx.2 ht₀.2⟩)
      t₀ ⟨hle, le_rfl⟩).symm

/-! ## Uniform local existence of unit-speed geodesic segments -/

/-- **Uniform local existence of unit-speed geodesic segments.**  At every point `x₀` there are
`ρ > 0` and an open neighbourhood `W` of `x₀` inside the chart at `x₀` such that for every `y ∈ W`
and every unit tangent vector `ξ ∈ T_yM` there is a curve `γ` on `Ioo (-(2ρ)) (2ρ)` with
`γ 0 = y`, `γ'(0) = ξ`, of constant speed `1`, `C^∞` and geodesic at every point of the interval. -/
theorem exists_local_geodesic_neighbourhood
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [I.Boundaryless] [ContMDiffCovariantDerivative cov ∞] [Nontrivial E]
    (hmet : IsMetricCompatible cov) (x₀ : M) :
    ∃ ρ : ℝ, ∃ W : Set M, 0 < ρ ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ (chartAt H x₀).source ∧
      (∀ y ∈ W, ∀ ξ : TangentSpace I y, ‖ξ‖ = 1 →
        ∃ γ : ℝ → M, γ 0 = y ∧ curveVelocity (I := I) γ 0 = ξ ∧
          ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (-(2 * ρ)) (2 * ρ)) ∧
          (∀ t ∈ Ioo (-(2 * ρ)) (2 * ρ), IsGeodesicAt cov γ t) ∧
          (∀ t ∈ Ioo (-(2 * ρ)) (2 * ρ), ‖curveVelocity (I := I) γ t‖ = 1)) := by
  classical
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨U, G, hUopen, hz0U, hUsub, hGU, hGsm, hG0⟩ :=
    exists_contMDiff_spray_extension (cov := cov) x₀
  obtain ⟨ρ₀, hρ₀, W', hW'open, hz0W', hW'sub, hunif⟩ :=
    Commons.Analysis.ODE.exists_uniform_secondOrderODE_solution_nhds (G := G) (U := U)
      (p₀ := (extChartAt I x₀) x₀) hUopen hz0U
      (fun z hz => (hGsm.contMDiffAt.contDiffAt).of_le (by norm_num)) hG0
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hW'open.mem_nhds hz0W')
  obtain ⟨K, hKcomp, hx₀K, hKsub⟩ :=
    exists_compact_subset (chartAt H x₀).open_source (mem_chart_source H x₀)
  have hKne : K.Nonempty := ⟨x₀, interior_subset hx₀K⟩
  obtain ⟨lam, hlam, Lam, hLam, hbounds⟩ :=
    ChartBounds.exists_chartGram_bounds (I := I) x₀ hKcomp hKne hKsub
  refine ⟨ρ₀ * Real.sqrt lam, interior K ∩ ((extChartAt I x₀).source ∩
      (fun y : M => ((extChartAt I x₀) y, (0 : E))) ⁻¹'
        Metric.ball ((extChartAt I x₀) x₀, (0 : E)) ε), ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_pos hρ₀ (Real.sqrt_pos.mpr hlam)
  · exact isOpen_interior.inter (((continuousOn_extChartAt (I := I) (x := x₀)).prodMk
      continuousOn_const).isOpen_inter_preimage
        (by rw [extChartAt_source]; exact (chartAt H x₀).open_source) isOpen_ball)
  · exact ⟨hx₀K, mem_extChartAt_source x₀,
      by rw [Set.mem_preimage, Metric.mem_ball, dist_self]; exact hε⟩
  · intro y hy
    simpa only [extChartAt_source] using hy.2.1
  · intro y hy ξ hξ
    have hyK : y ∈ K := interior_subset hy.1
    have hysrcE : y ∈ (extChartAt I x₀).source := hy.2.1
    have hysrc : y ∈ (chartAt H x₀).source := by rwa [extChartAt_source] at hysrcE
    have hyε : ((extChartAt I x₀) y, (0 : E)) ∈ Metric.ball ((extChartAt I x₀) x₀, (0 : E)) ε :=
      hy.2.2
    have hyW' : ((extChartAt I x₀) y, (0 : E)) ∈ W' := hεsub hyε
    set a : E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y ξ with ha
    have hsymm : (trivializationAt E (TangentSpace I) x₀).symmL ℝ y a = ξ :=
      Trivialization.symmL_continuousLinearMapAt (R := ℝ)
        (e := trivializationAt E (TangentSpace I) x₀) hysrc ξ
    have hacg : chartGram (I := I) x₀ y a a = 1 := by
      show inner ℝ ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y a)
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y a) = 1
      rw [hsymm, real_inner_self_eq_norm_sq, hξ, one_pow]
    have hnorm_le : Real.sqrt lam * ‖a‖ ≤ 1 := by
      have h := (hbounds y hyK a).1
      rw [hacg] at h
      have h2 : (Real.sqrt lam * ‖a‖) ^ 2 ≤ 1 := by
        rw [mul_pow, Real.sq_sqrt hlam.le]
        exact h
      nlinarith [Real.sqrt_nonneg lam, norm_nonneg a, h2]
    have hane : a ≠ 0 := by
      intro h0
      have hξ0 : ξ = 0 := by
        rw [← hsymm]
        simp only [h0, map_zero]
      rw [hξ0] at hξ
      simp at hξ
    have hnormane : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr hane
    have hVpos : 0 < ρ₀ / ‖a‖ := div_pos hρ₀ (norm_pos_iff.mpr hane)
    have hρle : ρ₀ * Real.sqrt lam ≤ ρ₀ / ‖a‖ := by
      rw [le_div_iff₀ (norm_pos_iff.mpr hane)]
      calc (ρ₀ * Real.sqrt lam) * ‖a‖ = ρ₀ * (Real.sqrt lam * ‖a‖) := by ring
        _ ≤ ρ₀ * 1 := mul_le_mul_of_nonneg_left hnorm_le hρ₀.le
        _ = ρ₀ := mul_one ρ₀
    have hvnorm : ‖(ρ₀ / ‖a‖) • a‖ = ρ₀ := by
      rw [norm_smul, Real.norm_of_nonneg hVpos.le,
        div_mul_cancel₀ _ hnormane]
    obtain ⟨u, wf, hu0, hw0, hmem, hdu, hdw⟩ :=
      hunif ((extChartAt I x₀) y, (0 : E)) hyW' ((ρ₀ / ‖a‖) • a) hvnorm.le
    have hstay_u : ∀ t ∈ Ioo (-2 : ℝ) 2, u t ∈ (extChartAt I x₀).target :=
      fun t ht => (hUsub (hmem t ht)).1
    have hdw' : ∀ t ∈ Ioo (-2 : ℝ) 2,
        HasDerivAt wf (chartGeodesicVectorField cov x₀ (u t, wf t)) t := by
      intro t ht
      have hd := hdw t ht
      rwa [hGU (u t, wf t) (hmem t ht)] at hd
    set c : ℝ := ‖a‖ / ρ₀ with hc
    have hcpos : 0 < c := div_pos (norm_pos_iff.mpr hane) hρ₀
    have hcne : c ≠ 0 := ne_of_gt hcpos
    set u₂ : ℝ → E := fun t => u (c * t) with hu₂
    set w₂ : ℝ → E := fun t => c • wf (c * t) with hw₂
    have hct : ∀ t ∈ Ioo (-(2 * (ρ₀ * Real.sqrt lam))) (2 * (ρ₀ * Real.sqrt lam)),
        c * t ∈ Ioo (-2 : ℝ) 2 := by
      intro t ht
      refine abs_lt.mp ?_
      rw [abs_mul, abs_of_pos hcpos]
      have htabs : |t| < 2 * (ρ₀ * Real.sqrt lam) := abs_lt.mpr ⟨ht.1, ht.2⟩
      calc c * |t| < c * (2 * (ρ₀ * Real.sqrt lam)) := mul_lt_mul_of_pos_left htabs hcpos
        _ = 2 * (Real.sqrt lam * ‖a‖) := by rw [hc]; field_simp
        _ ≤ 2 * 1 := by linarith [hnorm_le]
        _ = 2 := by norm_num
    have hAB : -(2 * (ρ₀ * Real.sqrt lam)) < 2 * (ρ₀ * Real.sqrt lam) := by
      have := mul_pos hρ₀ (Real.sqrt_pos.mpr hlam); linarith
    have hmem0 : (0 : ℝ) ∈ Ioo (-(2 * (ρ₀ * Real.sqrt lam))) (2 * (ρ₀ * Real.sqrt lam)) :=
      ⟨by linarith, by linarith⟩
    have hstay₂ : ∀ t ∈ Ioo (-(2 * (ρ₀ * Real.sqrt lam))) (2 * (ρ₀ * Real.sqrt lam)),
        u₂ t ∈ (extChartAt I x₀).target := fun t ht => hstay_u (c * t) (hct t ht)
    have hdu₂ : ∀ t ∈ Ioo (-(2 * (ρ₀ * Real.sqrt lam))) (2 * (ρ₀ * Real.sqrt lam)),
        HasDerivAt u₂ (w₂ t) t := by
      intro t ht
      have h := (hdu (c * t) (hct t ht)).scomp t (hasDerivAt_const_mul c)
      simpa only [hu₂, hw₂, Function.comp_def] using h
    have hdw₂ : ∀ t ∈ Ioo (-(2 * (ρ₀ * Real.sqrt lam))) (2 * (ρ₀ * Real.sqrt lam)),
        HasDerivAt w₂ (chartGeodesicVectorField cov x₀ (u₂ t, w₂ t)) t := by
      intro t ht
      have h1 : HasDerivAt (fun s => wf (c * s))
          (c • chartGeodesicVectorField cov x₀ (u (c * t), wf (c * t))) t :=
        (hdw' (c * t) (hct t ht)).scomp t (hasDerivAt_const_mul c)
      have h2 : HasDerivAt (fun s => c • wf (c * s))
          (c • (c • chartGeodesicVectorField cov x₀ (u (c * t), wf (c * t)))) t :=
        h1.const_smul c
      have h3 : c • (c • chartGeodesicVectorField cov x₀ (u (c * t), wf (c * t)))
          = chartGeodesicVectorField cov x₀ (u (c * t), c • wf (c * t)) := by
        rw [smul_smul, ← pow_two]
        rw [← chartGeodesicVectorField_smul cov x₀ c (u (c * t), wf (c * t))
          (hstay_u (c * t) (hct t ht))]
      rw [h3] at h2
      simpa only [hu₂, hw₂, Function.comp_def] using h2
    have hγ0 : (extChartAt I x₀).symm (u₂ 0) = y := by
      have h1 : u₂ 0 = (extChartAt I x₀) y := by
        show u (c * 0) = _
        rw [mul_zero]
        exact hu0
      rw [h1]
      exact (extChartAt I x₀).left_inv hysrcE
    have hw2 : w₂ 0 = c • ((ρ₀ / ‖a‖) • a) := by
      show c • wf (c * 0) = _
      rw [mul_zero, hw0]
    have hval0 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u₂ 0)) (w₂ 0) (w₂ 0) = 1 := by
      rw [hγ0, hw2, chartGram_smul_smul]
      have h2 : chartGram (I := I) x₀ y ((ρ₀ / ‖a‖) • a) ((ρ₀ / ‖a‖) • a)
          = (ρ₀ / ‖a‖) ^ 2 := by
        rw [chartGram_smul_smul, hacg, mul_one]
      rw [h2, hc]
      field_simp
    refine ⟨fun t => (extChartAt I x₀).symm (u₂ t), hγ0, ?_, ?_, ?_, ?_⟩
    · have hcv := curveVelocity_extChartAt_symm (I := I) (x₀ := x₀) (u := u₂) (t := 0) (v := w₂ 0)
        (hdu₂ 0 hmem0) (hstay₂ 0 hmem0)
        (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hmem0) hstay₂)
      rw [hcv, hγ0]
      rw [hw2, map_smul, map_smul, hsymm, smul_smul,
        show c * (ρ₀ / ‖a‖) = 1 from by rw [hc]; field_simp, one_smul]
    · exact GeodesicGlobal.contMDiffOn_chartCurve_of_chartODE (cov := cov) x₀ hstay₂ hdu₂ hdw₂
    · intro t ht
      exact GeodesicGlobal.isGeodesicAt_of_chartODE cov x₀ hAB ht hstay₂ hdu₂ hdw₂
    · intro t ht
      have hconst := chartGram_const_of_chartODE (cov := cov) hmet hstay₂ hdu₂ hdw₂ hmem0 t ht
      have hsq : ‖curveVelocity (I := I) (fun t => (extChartAt I x₀).symm (u₂ t)) t‖ ^ 2 = 1 := by
        have hcv := curveVelocity_extChartAt_symm (I := I) (x₀ := x₀) (u := u₂) (t := t)
          (v := w₂ t) (hdu₂ t ht) (hstay₂ t ht)
          (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) hstay₂)
        rw [hcv]
        have hb : ‖(trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm (u₂ t))
              (w₂ t)‖ ^ 2
            = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u₂ t)) (w₂ t) (w₂ t) := by
          show ‖(trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm (u₂ t))
              (w₂ t)‖ ^ 2
            = inner ℝ ((trivializationAt E (TangentSpace I) x₀).symmL ℝ
                ((extChartAt I x₀).symm (u₂ t)) (w₂ t))
              ((trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm (u₂ t))
                (w₂ t))
          rw [real_inner_self_eq_norm_sq]
        rw [hb, hconst, hval0]
      rcases sq_eq_one_iff.mp hsq with h | h
      · exact h
      · exfalso
        have := norm_nonneg (curveVelocity (I := I) (fun t => (extChartAt I x₀).symm (u₂ t)) t)
        linarith


/-! ## Time translation of a geodesic -/

/-- **The velocity of a time-shifted curve.** -/
lemma curveVelocity_comp_sub {σ : ℝ → M} {t T : ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ) I σ t) :
    curveVelocity (I := I) (fun s : ℝ => σ (s - T)) (t + T) = curveVelocity (I := I) σ t := by
  have hd' : MDifferentiableAt 𝓘(ℝ) I σ (1 * (t + T) + -T) := by
    rw [show 1 * (t + T) + -T = t from by ring]; exact hd
  have h2 : curveVelocity (I := I) (fun s : ℝ => σ (1 * s + -T)) (t + T)
      = curveVelocity (I := I) σ t := by
    have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := σ) (c := 1) (d := -T)
      (t := t + T) hd'
    rw [one_smul, show 1 * (t + T) + -T = t from by ring] at h
    exact h
  have hfun : (fun s : ℝ => σ (s - T)) = (fun s : ℝ => σ (1 * s + -T)) := by
    funext s; rw [one_mul, sub_eq_add_neg]
  exact (Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I)
    (Filter.EventuallyEq.of_eq hfun)).trans h2

/-- **Time translation preserves the geodesic equation.**  If `σ` is a geodesic at `t` and is
differentiable on a neighbourhood of `t`, then `s ↦ σ (s - T)` is a geodesic at `t + T`. -/
lemma isGeodesicAt_comp_sub {σ : ℝ → M} {t T : ℝ}
    (hmd : ∀ᶠ r in 𝓝 t, MDifferentiableAt 𝓘(ℝ) I σ r)
    (hgeo : IsGeodesicAt cov σ t) :
    IsGeodesicAt cov (fun s : ℝ => σ (s - T)) (t + T) := by
  intro Z hZ hZeq
  have hvel : curveVelocity (I := I) (fun s : ℝ => σ (s - T)) (t + T)
      = curveVelocity (I := I) σ t := curveVelocity_comp_sub (I := I) hmd.self_of_nhds
  have hbase : (fun s : ℝ => σ (s - T)) (t + T) = σ t := by
    show σ ((t + T) - T) = σ t
    rw [show (t + T) - T = t from by ring]
  have hZeq' : ∀ᶠ r in 𝓝 t, Z (σ r) = curveVelocity (I := I) σ r := by
    have h1 : ∀ᶠ r in 𝓝 t,
        Z (σ (r + T - T)) = curveVelocity (I := I) (fun s : ℝ => σ (s - T)) (r + T) :=
      (tendsto_id.add tendsto_const_nhds).eventually hZeq
    filter_upwards [h1, hmd] with r hr1 hr2
    have h2 : curveVelocity (I := I) (fun s : ℝ => σ (s - T)) (r + T)
        = curveVelocity (I := I) σ r := curveVelocity_comp_sub (I := I) hr2
    rw [h2] at hr1
    rw [show r + T - T = r from by ring] at hr1
    exact hr1
  rw [hbase, hvel]
  exact hgeo Z hZ hZeq'

/-! ## Gluing two geodesics at a common point -/

/-- **Gluing two geodesics with a common point and velocity.**  Let `γ` be a geodesic, `C^∞` on the
open interval `Ioo (-δ) (T + δ)`, and let `σ` be a geodesic through `γ T` with `σ'(0) = γ'(T)`,
`C^∞` on `Ioo (-δ') δ'`.  Then for any `δ'' ≤ δ'` the concatenation `glue γ σ T` is `C^∞` and a
geodesic on the whole interval `Ioo (-δ) (T + δ'')`. -/
theorem glue_geodesic
    [I.Boundaryless] [ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} {T δ δ' δ'' : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (-δ) (T + δ)))
    (hγgeo : ∀ t ∈ Ioo (-δ) (T + δ), IsGeodesicAt cov γ t)
    (hne : curveVelocity (I := I) γ T ≠ 0)
    {σ : ℝ → M} (hσ0 : σ 0 = γ T)
    (hσv : curveVelocity (I := I) σ 0 = curveVelocity (I := I) γ T)
    (hδ' : 0 < δ') (hσsm : ContMDiffOn 𝓘(ℝ) I ∞ σ (Ioo (-δ') δ'))
    (hσgeo : ∀ t ∈ Ioo (-δ') δ', IsGeodesicAt cov σ t)
    (hδ'' : 0 < δ'') (hδ''le : δ'' ≤ δ') :
    ContMDiffOn 𝓘(ℝ) I ∞ (GeodesicGlobal.glue γ σ T) (Ioo (-δ) (T + δ'')) ∧
      (∀ t ∈ Ioo (-δ) (T + δ''), IsGeodesicAt cov (GeodesicGlobal.glue γ σ T) t) ∧
      (GeodesicGlobal.glue γ σ T =ᶠ[𝓝 T] fun r : ℝ => σ (r - T)) := by
  classical
  have hTmem : T ∈ Ioo (-δ) (T + δ) := ⟨by linarith, by linarith⟩
  have h0mem : (0 : ℝ) ∈ Ioo (-δ') δ' := ⟨by linarith, by linarith⟩
  -- sections extending the velocity fields
  obtain ⟨Z, hZ, hZev⟩ := CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity
    (I := I) isOpen_Ioo hTmem hγsm hne
  have hne0 : curveVelocity (I := I) σ 0 ≠ 0 := by rw [hσv]; exact hne
  obtain ⟨W, hW, hWev⟩ := CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity
    (I := I) isOpen_Ioo h0mem hσsm hne0
  -- the chart data of `γ` near `T` and of `σ` near `0`, in the chart at `γ T`
  obtain ⟨δ₃, hδ₃, hsrc₃, -, hdγ, hwγ⟩ := GeodesicGlobal.chartODE_of_isGeodesic (cov := cov)
    (x₀ := γ T) (γ := γ) (V := Ioo (-δ) (T + δ)) isOpen_Ioo hTmem hγsm
    (mem_chart_source H (γ T)) hγgeo Z hZ hZev
  obtain ⟨ε, hε, hsrcσ, -, hdσ, hwσ⟩ := GeodesicGlobal.chartODE_of_isGeodesic (cov := cov)
    (x₀ := γ T) (γ := σ) (V := Ioo (-δ') δ') isOpen_Ioo h0mem hσsm
    (by rw [hσ0]; exact mem_chart_source H (γ T)) hσgeo W hW hWev
  -- the shifted chart data of `σ`
  set u : ℝ → E := fun s => (extChartAt I (γ T)) (σ s) with hudef
  set w : ℝ → E := fun s => deriv (fun r : ℝ => (extChartAt I (γ T)) (σ r)) s with hwdef
  have hdσ' : ∀ s ∈ Ioo (-ε) ε, HasDerivAt u (w s) s := fun s hs =>
    hdσ s (by rw [zero_sub, zero_add]; exact hs)
  have hwσ' : ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt w (chartGeodesicVectorField cov (γ T) (u s, w s)) s := fun s hs =>
    hwσ s (by rw [zero_sub, zero_add]; exact hs)
  set u₂ : ℝ → E := fun t => u (t - T) with hu₂def
  set w₂ : ℝ → E := fun t => w (t - T) with hw₂def
  have hd₂ : ∀ s ∈ Ioo (T - ε) (T + ε), HasDerivAt u₂ (w₂ s) s := by
    intro s hs
    have h := (hdσ' (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩).scomp s
      ((hasDerivAt_id s).sub_const T)
    simpa only [hu₂def, hw₂def, Function.comp_def, id_eq, one_smul] using h
  have hw₂ : ∀ s ∈ Ioo (T - ε) (T + ε),
      HasDerivAt w₂ (chartGeodesicVectorField cov (γ T) (u₂ s, w₂ s)) s := by
    intro s hs
    have h := (hwσ' (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩).scomp s
      ((hasDerivAt_id s).sub_const T)
    simpa only [hu₂def, hw₂def, Function.comp_def, id_eq, one_smul] using h
  have hstay₂ : ∀ s ∈ Ioo (T - ε) (T + ε), u₂ s ∈ (extChartAt I (γ T)).target := by
    intro s hs
    refine PartialEquiv.map_source (extChartAt I (γ T)) ?_
    rw [extChartAt_source]
    exact hsrcσ (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- the values at the junction
  have hu₂T : u₂ T = (extChartAt I (γ T)) (γ T) := by
    show (extChartAt I (γ T)) (σ (T - T)) = _
    rw [show T - T = (0:ℝ) from by ring, hσ0]
  have hw₂T : w₂ T = deriv (fun t : ℝ => (extChartAt I (γ T)) (γ t)) T := by
    have h1 : w₂ T = deriv (fun r : ℝ => (extChartAt I (γ T)) (σ r)) 0 := by
      show deriv (fun r : ℝ => (extChartAt I (γ T)) (σ r)) (T - T) = _
      rw [show T - T = (0:ℝ) from by ring]
    rw [h1]
    have hmdσ : MDifferentiableAt 𝓘(ℝ) I σ 0 :=
      (hσsm.contMDiffAt (isOpen_Ioo.mem_nhds h0mem)).mdifferentiableAt (by simp)
    rw [CurveField.deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (x := γ T) hmdσ
      (by rw [hσ0]; exact mem_chart_source H (γ T))]
    rw [hσ0, hσv]
    exact (CurveField.deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (x := γ T)
      ((hγsm.contMDiffAt (isOpen_Ioo.mem_nhds hTmem)).mdifferentiableAt (by simp))
      (mem_chart_source H (γ T))).symm
  -- a common interval
  set δ₄ : ℝ := min (min δ₃ ε) (T + δ) / 2 with hδ₄def
  have hδ₄pos : 0 < δ₄ := by
    rw [hδ₄def]; have := lt_min (lt_min hδ₃ hε) (by linarith : (0:ℝ) < T + δ); linarith
  have hδ₄₃ : δ₄ < δ₃ := by
    rw [hδ₄def]; have h1 := min_le_left (min δ₃ ε) (T + δ)
    have h2 := min_le_left δ₃ ε; linarith
  have hδ₄ε : δ₄ < ε := by
    rw [hδ₄def]; have h1 := min_le_left (min δ₃ ε) (T + δ)
    have h2 := min_le_right δ₃ ε; linarith
  have hδ₄T : δ₄ < T + δ := by
    rw [hδ₄def]; have h1 := min_le_right (min δ₃ ε) (T + δ); linarith
  have hsub₃ : Icc (T - δ₄) T ⊆ Ioo (T - δ₃) (T + δ₃) := fun t ht =>
    ⟨by linarith [ht.1, hδ₄₃], by linarith [ht.2, hδ₃]⟩
  have hsubε : Icc (T - δ₄) T ⊆ Ioo (T - ε) (T + ε) := fun t ht =>
    ⟨by linarith [ht.1, hδ₄ε], by linarith [ht.2, hε]⟩
  -- the open set on which the coordinate curve of `γ` is smooth
  have hWγ : IsOpen (Ioo (-δ) (T + δ) ∩ γ ⁻¹' (chartAt H (γ T)).source) := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact Filter.inter_mem (isOpen_Ioo.mem_nhds ht.1)
      ((hγsm.continuousOn.continuousAt (isOpen_Ioo.mem_nhds ht.1)).preimage_mem_nhds
        ((chartAt H (γ T)).open_source.mem_nhds ht.2))
  have hUcd : ContDiffOn ℝ ∞ (fun t : ℝ => (extChartAt I (γ T)) (γ t))
      (Ioo (-δ) (T + δ) ∩ γ ⁻¹' (chartAt H (γ T)).source) := by
    have hcomp : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => (extChartAt I (γ T)) (γ t))
        (Ioo (-δ) (T + δ) ∩ γ ⁻¹' (chartAt H (γ T)).source) :=
      (contMDiffOn_extChartAt (I := I) (x := γ T)).comp
        (hγsm.mono Set.inter_subset_left) (fun t ht => ht.2)
    exact hcomp.contDiffOn
  have hsubIcc : Icc (T - δ₄) T ⊆ Ioo (-δ) (T + δ) ∩ γ ⁻¹' (chartAt H (γ T)).source :=
    fun t ht => ⟨⟨by linarith [ht.1, hδ₄T, hδ], by linarith [ht.2, hδ]⟩,
      hsrc₃ t (hsub₃ ht)⟩
  have h1c : ContinuousOn (fun t : ℝ => ((extChartAt I (γ T)) (γ t),
      deriv (fun s : ℝ => (extChartAt I (γ T)) (γ s)) t)) (Icc (T - δ₄) T) :=
    (hUcd.continuousOn.mono hsubIcc).prodMk
      ((hUcd.continuousOn_deriv_of_isOpen hWγ
        (WithTop.coe_le_coe.mpr le_top : ((1 : ℕ∞) : ℕ∞ω) ≤ ∞)).mono hsubIcc)
  have h2c : ContinuousOn (fun t : ℝ => (u₂ t, w₂ t)) (Icc (T - δ₄) T) := by
    have h1 : ContinuousOn u₂ (Icc (T - δ₄) T) := fun t ht =>
      ((hd₂ t (hsubε ht)).continuousAt).continuousWithinAt
    have h2 : ContinuousOn w₂ (Icc (T - δ₄) T) := fun t ht =>
      ((hw₂ t (hsubε ht)).continuousAt).continuousWithinAt
    exact h1.prodMk h2
  -- the field of the ODE is `C¹` at the junction
  have hFT : ContDiffAt ℝ 1 (chartGeodesicVectorField cov (γ T))
      (((extChartAt I (γ T)) (γ T), deriv (fun s : ℝ => (extChartAt I (γ T)) (γ s)) T)) := by
    have hopen : IsOpen ((extChartAt I (γ T)).target ×ˢ (univ : Set E)) :=
      (isOpen_extChartAt_target (γ T)).prod isOpen_univ
    have hz : ((extChartAt I (γ T)) (γ T), deriv (fun s : ℝ => (extChartAt I (γ T)) (γ s)) T)
        ∈ (extChartAt I (γ T)).target ×ˢ (univ : Set E) :=
      ⟨PartialEquiv.map_source (extChartAt I (γ T)) (mem_extChartAt_source (γ T)),
        Set.mem_univ _⟩
    exact ((Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray
      (cov := cov) (γ T)).contDiffAt (hopen.mem_nhds hz)).of_le (by norm_num)
  -- one-sided uniqueness
  obtain ⟨a', ha'T, hEqU, hEqV⟩ :=
    Commons.Analysis.ODE.ODE_solution_unique_Icc_left_of_contDiffAt
      (F := chartGeodesicVectorField cov (γ T))
      (u₁ := fun t : ℝ => (extChartAt I (γ T)) (γ t))
      (v₁ := deriv fun t : ℝ => (extChartAt I (γ T)) (γ t))
      (u₂ := u₂) (v₂ := w₂) (a := T - δ₄) (b := T) (by linarith)
      hFT h1c h2c
      (fun t ht => ((hdγ t (hsub₃ ⟨le_of_lt ht.1, ht.2⟩)).prodMk
        (hwγ t (hsub₃ ⟨le_of_lt ht.1, ht.2⟩))).hasDerivWithinAt)
      (fun t ht => ((hd₂ t (hsubε ⟨le_of_lt ht.1, ht.2⟩)).prodMk
        (hw₂ t (hsubε ⟨le_of_lt ht.1, ht.2⟩))).hasDerivWithinAt)
      ⟨hu₂T.symm, hw₂T.symm⟩
  -- agreement of the two curves to the left of the junction
  set a'' : ℝ := max a' (T - δ₄) with ha''def
  have ha''T : a'' < T := max_lt ha'T (by linarith)
  have hagree : ∀ t ∈ Icc a'' T, γ t = σ (t - T) := by
    intro t ht
    have hsrc1 : γ t ∈ (extChartAt I (γ T)).source := by
      rw [extChartAt_source]
      exact hsrc₃ t (hsub₃ ⟨by linarith [ht.1, le_max_right a' (T - δ₄)], ht.2⟩)
    have hst : t - T ∈ Ioo (-ε) ε :=
      ⟨by linarith [ht.1, le_max_right a' (T - δ₄), hδ₄ε], by linarith [ht.2, hε]⟩
    have hsrc2 : σ (t - T) ∈ (extChartAt I (γ T)).source := by
      rw [extChartAt_source]
      exact hsrcσ (t - T) (by rw [zero_sub, zero_add]; exact hst)
    have h1 : (extChartAt I (γ T)) (γ t) = u₂ t :=
      hEqU ⟨le_trans (le_max_left a' (T - δ₄)) ht.1, ht.2⟩
    have h2 : (extChartAt I (γ T)) (σ (t - T)) = u₂ t := rfl
    exact PartialEquiv.injOn (extChartAt I (γ T)) hsrc1 hsrc2 (h1.trans h2.symm)
  -- the glued curve agrees with the shifted `σ` on a neighbourhood of the junction
  set b : ℝ := max a'' (T - δ'') with hbdef
  have hbT : b < T := max_lt ha''T (by linarith)
  have hble : T - δ'' ≤ b := by rw [hbdef]; exact le_max_right _ _
  have hbge : a'' ≤ b := by rw [hbdef]; exact le_max_left _ _
  have hglue_eq : ∀ t ∈ Ioo b (T + δ''),
      GeodesicGlobal.glue γ σ T t = σ (t - T) := by
    intro t ht
    by_cases hle : t ≤ T
    · rw [GeodesicGlobal.glue_of_le hle]
      exact hagree t ⟨le_trans (le_max_left a'' (T - δ'')) (le_of_lt ht.1), hle⟩
    · rw [GeodesicGlobal.glue_of_lt (not_le.mp hle)]
  -- the shifted `σ` is smooth and geodesic on the whole interval
  have hshift_sm : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => σ (s - T)) (Ioo (T - δ'') (T + δ'')) := by
    have hinner : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => s - T)
        (Ioo (T - δ'') (T + δ'')) := contMDiffOn_id.sub contMDiffOn_const
    have hcomp : ContMDiffOn 𝓘(ℝ) I ∞ (σ ∘ fun s : ℝ => s - T) (Ioo (T - δ'') (T + δ'')) :=
      hσsm.comp hinner (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    simpa only [Function.comp_def] using hcomp
  have hshift_geo : ∀ s ∈ Ioo (T - δ'') (T + δ''),
      IsGeodesicAt cov (fun r : ℝ => σ (r - T)) s := by
    intro s hs
    have ht : s - T ∈ Ioo (-δ') δ' := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h := isGeodesicAt_comp_sub (cov := cov) (σ := σ) (t := s - T) (T := T)
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht)
        (fun r hr => (hσsm.contMDiffAt (isOpen_Ioo.mem_nhds hr)).mdifferentiableAt (by simp)))
      (hσgeo (s - T) ht)
    rwa [show s - T + T = s from by ring] at h
  have hglue_ev : GeodesicGlobal.glue γ σ T =ᶠ[𝓝 T] fun r : ℝ => σ (r - T) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ⟨hbT, by linarith [hδ'']⟩)
      (fun t ht => hglue_eq t ht)
  refine ⟨?_, ?_, hglue_ev⟩
  · -- smoothness of the glued curve
    apply contMDiffOn_of_locally_contMDiffOn
    intro t ht
    rcases lt_or_ge t T with hlt | hge
    · refine ⟨Ioo (-δ) T, isOpen_Ioo, ⟨ht.1, hlt⟩, ?_⟩
      refine (hγsm.mono ?_).congr ?_
      · intro u hu; exact ⟨hu.2.1, by linarith [hu.2.2, hδ]⟩
      · intro u hu; exact GeodesicGlobal.glue_of_le (le_of_lt hu.2.2)
    · refine ⟨Ioo b (T + δ''), isOpen_Ioo, ⟨by linarith [hbT, hge], ht.2⟩, ?_⟩
      refine (hshift_sm.mono ?_).congr ?_
      · intro u hu; exact ⟨by linarith [hu.2.1, hble], hu.2.2⟩
      · intro u hu; exact hglue_eq u hu.2
  · -- the geodesic equation
    intro t ht
    rcases lt_or_ge t T with hlt | hge
    · have hev : GeodesicGlobal.glue γ σ T =ᶠ[𝓝 t] γ :=
        Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hlt)
          (fun r hr => GeodesicGlobal.glue_of_le hr.le)
      exact (Submission.GeodesicExtend.isGeodesicAt_congr_of_eventuallyEq (I := I) hev).mpr
        (hγgeo t ⟨ht.1, by linarith [hlt]⟩)
    · have hev : GeodesicGlobal.glue γ σ T =ᶠ[𝓝 t] (fun r : ℝ => σ (r - T)) :=
        Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ⟨by linarith [hbT, hge], ht.2⟩)
          (fun r hr => hglue_eq r hr)
      exact (Submission.GeodesicExtend.isGeodesicAt_congr_of_eventuallyEq (I := I) hev).mpr
        (hshift_geo t ⟨by linarith [hge, hδ''], ht.2⟩)

/-! ## The uniform radius over a compact manifold -/

/-- **Uniform radius for geodesic segments.**  On a compact manifold there is `δ > 0` such that
for every point `x` and every unit tangent vector `ξ` at `x` there is a curve on `Ioo (-(2δ)) (2δ)`
with `γ 0 = x`, `γ'(0) = ξ`, of constant speed `1`, geodesic and `C^∞` at every point of the
interval.  (The proof covers `M` by finitely many of the neighbourhoods produced by
`exists_local_geodesic_neighbourhood` and takes the minimum of the corresponding radii.) -/
theorem exists_uniform_geodesic_segment
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [I.Boundaryless] [ContMDiffCovariantDerivative cov ∞] [Nontrivial E] [CompactSpace M]
    (hmet : IsMetricCompatible cov) :
    ∃ δ > 0, ∀ x : M, ∀ ξ : TangentSpace I x, ‖ξ‖ = 1 →
      ∃ γ : ℝ → M, γ 0 = x ∧ curveVelocity (I := I) γ 0 = ξ ∧
        ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (-(2 * δ)) (2 * δ)) ∧
        (∀ t ∈ Ioo (-(2 * δ)) (2 * δ), IsGeodesicAt cov γ t) ∧
        (∀ t ∈ Ioo (-(2 * δ)) (2 * δ), ‖curveVelocity (I := I) γ t‖ = 1) := by
  classical
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    choose ρ W hρ hWopen hxW hWsub hWgood using fun x =>
      exists_local_geodesic_neighbourhood (cov := cov) hmet x
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWopen
      (fun y _ => Set.mem_iUnion.mpr ⟨y, hxW y⟩)
    have htne : t.Nonempty := by
      obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x₀))
      exact ⟨i, hi⟩
    refine ⟨(t.image ρ).min' (Finset.image_nonempty.mpr htne), ?_, ?_⟩
    · refine (Finset.lt_min'_iff (t.image ρ) (Finset.image_nonempty.mpr htne)).mpr ?_
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact hρ i
    · intro x ξ hξ
      obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      obtain ⟨γ, hγ0, hγv, hγsm, hγgeo, hγsp⟩ := hWgood i x hxi ξ hξ
      have hδle : (t.image ρ).min' (Finset.image_nonempty.mpr htne) ≤ ρ i :=
        Finset.min'_le (t.image ρ) (ρ i) (Finset.mem_image.mpr ⟨i, hit, rfl⟩)
      have hsub : Ioo (-(2 * (t.image ρ).min' (Finset.image_nonempty.mpr htne)))
          (2 * (t.image ρ).min' (Finset.image_nonempty.mpr htne))
          ⊆ Ioo (-(2 * ρ i)) (2 * ρ i) :=
        fun s hs => ⟨by linarith [hs.1, hδle], by linarith [hs.2, hδle]⟩
      exact ⟨γ, hγ0, hγv, hγsm.mono hsub, fun s hs => hγgeo s (hsub hs),
        fun s hs => hγsp s (hsub hs)⟩
  · exact ⟨1, one_pos, fun x => (hM ⟨x⟩).elim⟩

/-! ## Geodesic segments of prescribed length -/

/-- **Geodesic segments of prescribed length.**  On a compact manifold there is `δ > 0` such that
for every `T ≥ 0`, every point `x` and every unit tangent vector `ξ` at `x` there is a curve `γ`
with `γ 0 = x`, `γ'(0) = ξ`, of constant speed `1`, `C^∞` and geodesic on the whole interval
`Ioo (-δ) (T + δ)`.

The proof iterates the local existence (`exists_uniform_geodesic_segment`) with the gluing theorem
`glue_geodesic`: with `h = δ₀/2` the local existence gives a geodesic on `Ioo (-h) (2h)`, and if
one exists on `Ioo (-h) R` with `R ≥ h` then gluing the next local segment at `T = R - h` extends
it to `Ioo (-h) (R + 2h)`.  Induction on the number of steps gives a geodesic of any length. -/
theorem exists_geodesic_segment
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [I.Boundaryless] [ContMDiffCovariantDerivative cov ∞] [Nontrivial E] [CompactSpace M]
    (hmet : IsMetricCompatible cov) :
    ∃ δ > 0, ∀ T : ℝ, 0 ≤ T → ∀ x : M, ∀ ξ : TangentSpace I x, ‖ξ‖ = 1 →
      ∃ γ : ℝ → M, γ 0 = x ∧ curveVelocity (I := I) γ 0 = ξ ∧
        ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (-δ) (T + δ)) ∧
        (∀ t ∈ Ioo (-δ) (T + δ), IsGeodesicAt cov γ t) ∧
        (∀ t ∈ Ioo (-δ) (T + δ), ‖curveVelocity (I := I) γ t‖ = 1) := by
  classical
  obtain ⟨δ₀, hδ₀, hunif⟩ := exists_uniform_geodesic_segment (cov := cov) hmet
  set h : ℝ := δ₀ / 2 with hh
  have hhpos : 0 < h := by rw [hh]; linarith
  have hh4 : h ≤ δ₀ := by rw [hh]; linarith
  have h2 : 2 * δ₀ = 4 * h := by rw [hh]; ring
  have h3 : 3 * h ≤ 2 * δ₀ := by rw [h2]; linarith
  have h2h : 0 < 2 * h := by linarith
  -- the base statement: reach `2h`
  have hbase : ∀ x : M, ∀ ξ : TangentSpace I x, ‖ξ‖ = 1 →
      ∃ γ : ℝ → M, γ 0 = x ∧ curveVelocity (I := I) γ 0 = ξ ∧
        ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (-h) (2 * h)) ∧
        (∀ t ∈ Ioo (-h) (2 * h), IsGeodesicAt cov γ t) ∧
        (∀ t ∈ Ioo (-h) (2 * h), ‖curveVelocity (I := I) γ t‖ = 1) := by
    intro x ξ hξ
    obtain ⟨γ, hγ0, hγv, hγsm, hγgeo, hγsp⟩ := hunif x ξ hξ
    have hsub : Ioo (-h) (2 * h) ⊆ Ioo (-(2 * δ₀)) (2 * δ₀) := fun s hs =>
      ⟨by linarith [hs.1], by linarith [hs.2, hh4]⟩
    exact ⟨γ, hγ0, hγv, hγsm.mono hsub, fun t ht => hγgeo t (hsub ht),
      fun t ht => hγsp t (hsub ht)⟩
  -- one step: reach `R` ⟹ reach `R + 2h`
  have hstep : ∀ R : ℝ, h < R →
      (∀ x : M, ∀ ξ : TangentSpace I x, ‖ξ‖ = 1 →
        ∃ γ : ℝ → M, γ 0 = x ∧ curveVelocity (I := I) γ 0 = ξ ∧
          ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (-h) R) ∧
          (∀ t ∈ Ioo (-h) R, IsGeodesicAt cov γ t) ∧
          (∀ t ∈ Ioo (-h) R, ‖curveVelocity (I := I) γ t‖ = 1)) →
      (∀ x : M, ∀ ξ : TangentSpace I x, ‖ξ‖ = 1 →
        ∃ γ : ℝ → M, γ 0 = x ∧ curveVelocity (I := I) γ 0 = ξ ∧
          ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (-h) (R + 2 * h)) ∧
          (∀ t ∈ Ioo (-h) (R + 2 * h), IsGeodesicAt cov γ t) ∧
          (∀ t ∈ Ioo (-h) (R + 2 * h), ‖curveVelocity (I := I) γ t‖ = 1)) := by
    intro R hR hP x ξ hξ
    obtain ⟨γ, hγ0, hγv, hγsm, hγgeo, hγsp⟩ := hP x ξ hξ
    set T : ℝ := R - h with hTdef
    have hTpos : 0 < T := by rw [hTdef]; linarith [hR]
    have hTh : T + h = R := by rw [hTdef]; ring
    have hTmem : T ∈ Ioo (-h) R := by
      refine ⟨by linarith [hTpos, hhpos], ?_⟩
      rw [hTdef]; linarith
    have hη : ‖curveVelocity (I := I) γ T‖ = 1 := hγsp T hTmem
    have hne : curveVelocity (I := I) γ T ≠ 0 := by
      intro h0
      rw [h0] at hη
      norm_num at hη
    obtain ⟨σ, hσ0, hσv, hσsm, hσgeo, hσsp⟩ := hunif (γ T) (curveVelocity (I := I) γ T) hη
    have hγsm' : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (-h) (T + h)) := by
      rw [hTh]; exact hγsm
    have hγgeo' : ∀ t ∈ Ioo (-h) (T + h), IsGeodesicAt cov γ t := by
      intro t ht; rw [hTh] at ht; exact hγgeo t ht
    obtain ⟨hglue_sm, hglue_geo, hglue_ev⟩ := glue_geodesic (cov := cov) (γ := γ) (σ := σ) (T := T)
      (δ := h) (δ' := 2 * δ₀) (δ'' := 3 * h) hTpos hhpos hγsm' hγgeo' hne
      hσ0 hσv (by linarith) hσsm hσgeo (by linarith) h3
    have hT3 : T + 3 * h = R + 2 * h := by rw [hTdef]; ring
    have hsm' : ContMDiffOn 𝓘(ℝ) I ∞ (GeodesicGlobal.glue γ σ T) (Ioo (-h) (R + 2 * h)) := by
      rw [← hT3]; exact hglue_sm
    have hgeo' : ∀ t ∈ Ioo (-h) (R + 2 * h),
        IsGeodesicAt cov (GeodesicGlobal.glue γ σ T) t := by
      intro t ht; rw [← hT3] at ht; exact hglue_geo t ht
    refine ⟨GeodesicGlobal.glue γ σ T, ?_, ?_, hsm', hgeo', ?_⟩
    · rw [GeodesicGlobal.glue_of_le hTpos.le]
      exact hγ0
    · have hev : GeodesicGlobal.glue γ σ T =ᶠ[𝓝 (0:ℝ)] γ :=
        Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hTpos)
          (fun r hr => GeodesicGlobal.glue_of_le hr.le)
      rw [Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hev, hγv]
    · intro t ht
      rw [← hT3] at ht
      rcases lt_or_ge t T with hlt | hge
      · have hev : GeodesicGlobal.glue γ σ T =ᶠ[𝓝 t] γ :=
          Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hlt)
            (fun r hr => GeodesicGlobal.glue_of_le hr.le)
        rw [hev.eq_of_nhds]
        rw [Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hev]
        exact hγsp t ⟨ht.1, by linarith [hlt, hTh]⟩
      · have hb : GeodesicGlobal.glue γ σ T t = σ (t - T) := by
          rcases eq_or_lt_of_le hge with hEq | hLt
          · rw [← hEq, GeodesicGlobal.glue_of_le le_rfl]
            show γ T = σ (T - T)
            rw [show T - T = (0:ℝ) from by ring]
            exact hσ0.symm
          · exact GeodesicGlobal.glue_of_lt hLt
        have hev : GeodesicGlobal.glue γ σ T =ᶠ[𝓝 t] (fun r : ℝ => σ (r - T)) := by
          rcases eq_or_lt_of_le hge with hEq | hLt
          · rw [← hEq]; exact hglue_ev
          · exact Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ⟨hLt, ht.2⟩)
              (fun r hr => GeodesicGlobal.glue_of_lt hr.1)
        rw [hb]
        rw [Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hev]
        have hmem : t - T ∈ Ioo (-(2 * δ₀)) (2 * δ₀) :=
          ⟨by linarith [hge], by linarith [ht.2, h3]⟩
        have hcv : curveVelocity (I := I) (fun r : ℝ => σ (r - T)) t
            = curveVelocity (I := I) σ (t - T) := by
          have hmd : MDifferentiableAt 𝓘(ℝ) I σ (t - T) :=
            (hσsm.contMDiffAt (isOpen_Ioo.mem_nhds hmem)).mdifferentiableAt (by simp)
          have hc := curveVelocity_comp_sub (I := I) (σ := σ) (t := t - T) (T := T) hmd
          rwa [show t - T + T = t from by ring] at hc
        rw [hcv]
        exact hσsp (t - T) hmem
  -- iterate the step
  have key : ∀ N : ℕ,
      (∀ x : M, ∀ ξ : TangentSpace I x, ‖ξ‖ = 1 →
        ∃ γ : ℝ → M, γ 0 = x ∧ curveVelocity (I := I) γ 0 = ξ ∧
          ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (-h) (2 * h + (N : ℝ) * (2 * h))) ∧
          (∀ t ∈ Ioo (-h) (2 * h + (N : ℝ) * (2 * h)), IsGeodesicAt cov γ t) ∧
          (∀ t ∈ Ioo (-h) (2 * h + (N : ℝ) * (2 * h)),
            ‖curveVelocity (I := I) γ t‖ = 1)) := by
    intro N
    induction N with
    | zero =>
      have h0 : 2 * h + ((0 : ℕ) : ℝ) * (2 * h) = 2 * h := by push_cast; ring
      rw [h0]
      exact hbase
    | succ N ih =>
      have hidx : 2 * h + ((N : ℝ) + 1) * (2 * h) = 2 * h + (N : ℝ) * (2 * h) + 2 * h := by ring
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hstep' := hstep (2 * h + (N : ℝ) * (2 * h)) (by nlinarith [hhpos, hN0]) ih
      push_cast
      rw [hidx]
      exact hstep'
  -- any length
  refine ⟨h, hhpos, fun T _ x ξ hξ => ?_⟩
  obtain ⟨γ, hγ0, hγv, hγsm, hγgeo, hγsp⟩ := key (Nat.ceil (T / (2 * h))) x ξ hξ
  have hNge : T ≤ ((Nat.ceil (T / (2 * h))) : ℕ) * (2 * h) := by
    have hc := Nat.le_ceil (T / (2 * h))
    rw [div_le_iff₀ h2h] at hc
    exact hc
  have hsub : Ioo (-h) (T + h) ⊆ Ioo (-h) (2 * h + ((Nat.ceil (T / (2 * h))) : ℕ) * (2 * h)) := by
    intro s hs
    exact ⟨hs.1, by linarith [hs.2, hNge]⟩
  exact ⟨γ, hγ0, hγv, hγsm.mono hsub, fun t ht => hγgeo t (hsub ht),
    fun t ht => hγsp t (hsub ht)⟩

end

end Submission.GeodesicGlobal2
