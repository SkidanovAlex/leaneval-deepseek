import Submission.BonnetMyers2
import Submission.JacobiGen

/-!
# Bonnet–Myers for a chart geodesic: the test-field instantiation

`Submission/BonnetMyers2.lean` reduces the chart-local Bonnet–Myers theorem to an *input inequality*
(`hInt`) for a variation field.  This file supplies that input for the classic test field
`η t = sin (π t / L) • Y t`, where `Y` is a parallel field of unit length orthogonal to the velocity
(the field produced by `JacobiGen.exists_parallel_unit_orthogonal_Ioo`).

The main result is `chart_BonnetMyers`: a solution of the chart geodesic equation on an interval
`Ioo A B` containing `[-1, L+2]`, which is unit speed at `0` and minimising on `[0,L]`
(`d(γ 0, γ L) = L`), satisfies `L ≤ π`.

## Contents

* `penv`, `penv'`: the coordinate expression of the parallel derivative of `Y` and its derivative;
* `tfd`, `tfd'`: the derivative of the test field, written with `penv` instead of `deriv Y`, and its
  derivative;
* `hasDerivAt_penv`, `hasDerivAt_tfd`, `continuousOn_tfd'`: the differentiability statements needed
  by `BonnetMyers.famEnergy_second_deriv_eq`;
* `exists_fam_mem_target`: the tube statement that the straight-line variation of the geodesic
  stays in the chart for small `s`;
* `chart_BonnetMyers`: the theorem.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Length
open Submission.GeodesicSpeed
open Submission.Jacobi
open Submission.JacobiGen
open Submission.ChartCurv
open Submission.ChartConnection
open Submission.ChartBounds
open Submission.SecondVariation
open Submission.IndexForm
open Submission.IndexForm2
open Submission.BonnetMyers
open Submission.BonnetMyers2

namespace Submission.BonnetMyers3

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## The coordinate fields attached to the test field -/

/-- The coordinate expression of the parallel derivative of `Y`: `-Γ(Y)(w)`. -/
noncomputable def penv (x₀ : M) (u w Y : ℝ → E) : ℝ → E := fun t =>
  -(chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t))

/-- The derivative of `penv` along the geodesic. -/
noncomputable def penv' (x₀ : M) (u w w' Y : ℝ → E) : ℝ → E := fun t =>
  -(dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (Y t) (w t)
    + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (penv (cov := cov) x₀ u w Y t) (w t)
    + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w' t))

/-- The derivative of the test field `sin (π t / L) • Y t`, written using `penv` instead of
`deriv Y`. -/
noncomputable def tfd (x₀ : M) (u w Y : ℝ → E) (L : ℝ) : ℝ → E := fun t =>
  (Real.pi / L * Real.cos (Real.pi * t / L)) • Y t
    + Real.sin (Real.pi * t / L) • penv (cov := cov) x₀ u w Y t

/-- The derivative of `tfd`. -/
noncomputable def tfd' (x₀ : M) (u w w' Y : ℝ → E) (L : ℝ) : ℝ → E := fun t =>
  (-(Real.pi / L) ^ 2 * Real.sin (Real.pi * t / L)) • Y t
    + (Real.pi / L * Real.cos (Real.pi * t / L)) • penv (cov := cov) x₀ u w Y t
    + (Real.pi / L * Real.cos (Real.pi * t / L)) • penv (cov := cov) x₀ u w Y t
    + Real.sin (Real.pi * t / L) • penv' (cov := cov) x₀ u w w' Y t

/-! ## Derivatives of the auxiliary fields -/

/-- The derivative of `penv` is `penv'`. -/
lemma hasDerivAt_penv [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u w w' Y : ℝ → E} {t : ℝ}
    (hu : HasDerivAt u (w t) t) (hY : HasDerivAt Y (penv (cov := cov) x₀ u w Y t) t)
    (hw : HasDerivAt w (w' t) t)
    (htgt : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ r in 𝓝 t, u r ∈ (extChartAt I x₀).target) :
    HasDerivAt (penv (cov := cov) x₀ u w Y) (penv' (cov := cov) x₀ u w w' Y t) t := by
  have h := hasDerivAt_chrB_curve (cov := cov) (x₀ := x₀) (u := u) (a := Y) (b := w)
    (v := w t) (a' := penv (cov := cov) x₀ u w Y t) (b' := w' t) hu hY hw htgt hstay
  have h2 : HasDerivAt (fun r : ℝ => - chrB cov x₀ ((extChartAt I x₀).symm (u r)) (Y r) (w r))
      (-(dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (Y t) (w t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (penv (cov := cov) x₀ u w Y t) (w t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w' t))) t := h.neg
  have hfun : (fun r : ℝ => - chrB cov x₀ ((extChartAt I x₀).symm (u r)) (Y r) (w r))
      = penv (cov := cov) x₀ u w Y := rfl
  rw [hfun] at h2
  exact h2

/-- The derivative of the test field is `tfd`. -/
lemma hasDerivAt_testField' {x₀ : M} {u w Y : ℝ → E} {L t : ℝ}
    (hY : HasDerivAt Y (penv (cov := cov) x₀ u w Y t) t) :
    HasDerivAt (testField (E := E) L Y) (tfd (cov := cov) x₀ u w Y L t) t := by
  have h := hasDerivAt_testField (L := L) (Y := Y) (t := t)
    hY.differentiableAt.hasDerivAt
  refine h.congr_deriv ?_
  rw [testFieldDeriv, hY.deriv]
  rfl


/-- The derivative of `t ↦ π/L · cos (π t / L)`. -/
lemma hasDerivAt_cos_pi (L t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.pi / L * Real.cos (Real.pi * t / L))
      (-(Real.pi / L) ^ 2 * Real.sin (Real.pi * t / L)) t := by
  have hinner : HasDerivAt (fun t : ℝ => Real.pi * t / L) (Real.pi / L) t := by
    have h1 : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi t := by
      have h := (hasDerivAt_id t).const_mul Real.pi
      have hfun : (fun y : ℝ => Real.pi * id y) = fun t : ℝ => Real.pi * t := by
        funext y; rfl
      rw [hfun] at h
      simpa using h
    exact h1.div_const L
  have hcos := (Real.hasDerivAt_cos (Real.pi * t / L)).comp t hinner
  have h2 := hcos.const_mul (Real.pi / L)
  refine h2.congr_deriv ?_
  ring

/-- **The derivative of `tfd`.** -/
lemma hasDerivAt_tfd [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u w w' Y : ℝ → E} {L t : ℝ}
    (hu : HasDerivAt u (w t) t) (hY : HasDerivAt Y (penv (cov := cov) x₀ u w Y t) t)
    (hw : HasDerivAt w (w' t) t)
    (htgt : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ r in 𝓝 t, u r ∈ (extChartAt I x₀).target) :
    HasDerivAt (tfd (cov := cov) x₀ u w Y L) (tfd' (cov := cov) x₀ u w w' Y L t) t := by
  have hpenv := hasDerivAt_penv (cov := cov) hu hY hw htgt hstay
  have h1 := (hasDerivAt_cos_pi L t).smul hY
  have h2 := (hasDerivAt_sin_pi L t).smul hpenv
  have h3 := h1.add h2
  refine h3.congr_deriv ?_
  simp only [tfd', penv]
  module

/-- **Continuity of `tfd'` on `[0,L]`.** -/
lemma continuousOn_tfd' [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u w w' Y : ℝ → E} {L : ℝ}
    (hu : ContinuousOn u (Icc (0:ℝ) L)) (hw : ContinuousOn w (Icc (0:ℝ) L))
    (hw' : ContinuousOn w' (Icc (0:ℝ) L)) (hY : ContinuousOn Y (Icc (0:ℝ) L))
    (hmem : ∀ t ∈ Icc (0:ℝ) L, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (tfd' (cov := cov) x₀ u w w' Y L) (Icc (0:ℝ) L) := by
  have hγ : ContinuousOn (fun t : ℝ => (extChartAt I x₀).symm (u t)) (Icc (0:ℝ) L) :=
    continuousOn_chartCurve hu hmem
  have hsrc : ∀ t ∈ Icc (0:ℝ) L, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (hmem t ht)
  have hp : ContinuousOn (penv (cov := cov) x₀ u w Y) (Icc (0:ℝ) L) :=
    (continuousOn_chrB_curve (cov := cov) hγ hY hw hsrc).neg
  have hp' : ContinuousOn (penv' (cov := cov) x₀ u w w' Y) (Icc (0:ℝ) L) := by
    have h1 : ContinuousOn (fun t : ℝ => dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (Y t) (w t))
        (Icc (0:ℝ) L) := continuousOn_dB_curve (cov := cov) hγ hw hY hw hsrc
    have h2 : ContinuousOn (fun t : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (u t))
        (penv (cov := cov) x₀ u w Y t) (w t)) (Icc (0:ℝ) L) :=
      continuousOn_chrB_curve (cov := cov) hγ hp hw hsrc
    have h3 : ContinuousOn (fun t : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w' t))
        (Icc (0:ℝ) L) := continuousOn_chrB_curve (cov := cov) hγ hY hw' hsrc
    rw [show penv' (cov := cov) x₀ u w w' Y = fun t : ℝ =>
        -(dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (Y t) (w t)
          + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (penv (cov := cov) x₀ u w Y t) (w t)
          + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w' t)) from rfl]
    exact ((h1.add h2).add h3).neg
  have hc : ContinuousOn (fun t : ℝ => -(Real.pi / L) ^ 2 * Real.sin (Real.pi * t / L))
      (Icc (0:ℝ) L) := by fun_prop
  have hc2 : ContinuousOn (fun t : ℝ => Real.pi / L * Real.cos (Real.pi * t / L))
      (Icc (0:ℝ) L) := by fun_prop
  have hs : ContinuousOn (fun t : ℝ => Real.sin (Real.pi * t / L)) (Icc (0:ℝ) L) := by fun_prop
  rw [show tfd' (cov := cov) x₀ u w w' Y L = fun t : ℝ =>
      (-(Real.pi / L) ^ 2 * Real.sin (Real.pi * t / L)) • Y t
        + (Real.pi / L * Real.cos (Real.pi * t / L)) • penv (cov := cov) x₀ u w Y t
        + (Real.pi / L * Real.cos (Real.pi * t / L)) • penv (cov := cov) x₀ u w Y t
        + Real.sin (Real.pi * t / L) • penv' (cov := cov) x₀ u w w' Y t from rfl]
  exact (((hc.smul hY).add (hc2.smul hp)).add (hc2.smul hp)).add (hs.smul hp')


/-! ## The variation stays in the chart for small `s` -/

/-- **The straight-line variation stays in the chart target for small `s`.**  This is the compactness
("tube") argument: the image of the (compact) interval under `u` is a compact subset of the open
chart target, so it has a positive distance to the complement, and the perturbation `s • η t` is
bounded. -/
lemma exists_fam_mem_target {x₀ : M} {u η : ℝ → E} {c d : ℝ}
    (hu : ContinuousOn u (Icc c d)) (hη : ContinuousOn η (Icc c d))
    (hmem : ∀ t ∈ Icc c d, u t ∈ (extChartAt I x₀).target) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc (-δ) δ, ∀ t ∈ Icc c d,
      u t + s • η t ∈ (extChartAt I x₀).target := by
  set K : Set E := u '' Icc c d with hKdef
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hu
  have hKU : K ⊆ (extChartAt I x₀).target := by
    rintro x ⟨t, ht, rfl⟩
    exact hmem t ht
  obtain ⟨ε, hεpos, hε⟩ := hK.exists_thickening_subset_open (isOpen_extChartAt_target x₀) hKU
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hη
  refine ⟨ε / (max M 0 + 1), div_pos hεpos (by linarith [le_max_right M 0]), ?_⟩
  intro s hs t ht
  refine hε ?_
  rw [Metric.mem_thickening_iff]
  refine ⟨u t, ⟨t, ht, rfl⟩, ?_⟩
  have h1 : dist (u t + s • η t) (u t) = ‖s • η t‖ := by
    rw [dist_eq_norm, add_sub_cancel_left]
  rw [h1, norm_smul]
  have hsabs : ‖s‖ ≤ ε / (max M 0 + 1) := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hs.1], hs.2⟩
  have hMle : M ≤ max M 0 := le_max_left _ _
  have hM0 : (0:ℝ) ≤ max M 0 := le_max_right _ _
  have hden : (0:ℝ) < max M 0 + 1 := by linarith
  calc ‖s‖ * ‖η t‖ ≤ ε / (max M 0 + 1) * max M 0 := by
        refine mul_le_mul hsabs (le_trans (hM t ht) hMle) (norm_nonneg _) (by positivity)
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
        nlinarith [hεpos]

/-! ## The chart-local Bonnet–Myers theorem -/

/-- **Bonnet–Myers (chart-local form).**  A unit-speed solution `u` of the chart geodesic equation
on an interval `Ioo A B` containing `[-1, L+2]`, which is minimising on `[0,L]`
(`d(γ 0, γ L) = L`), satisfies `L ≤ π`. -/
theorem chart_BonnetMyers [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {x₀ : M} {u w : ℝ → E} {A B L : ℝ} (hL : 0 < L) (hA : A < -1) (hB : L + 2 < B)
    (hstay_u : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Ioo A B, HasDerivAt w (chartGeodesicVectorField cov x₀ (u t, w t)) t)
    (hunit : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) (w 0) (w 0) = 1)
    (hmin : Manifold.riemannianEDist I ((extChartAt I x₀).symm (u 0)) ((extChartAt I x₀).symm (u L))
      = ENNReal.ofReal L) :
    L ≤ Real.pi := by
  classical
  have hA1 : (-1 : ℝ) < L + 2 := by linarith
  -- intervals
  have hsubL : Icc (0:ℝ) L ⊆ Ioo A B := fun t ht =>
    ⟨by linarith [hA, ht.1], by linarith [hB, ht.2]⟩
  have hsubM : Icc (-1:ℝ) (L+2) ⊆ Ioo A B := fun t ht =>
    ⟨by linarith [hA, ht.1], by linarith [hB, ht.2]⟩
  have hsubLM : Icc (0:ℝ) L ⊆ Icc (-1:ℝ) (L+2) := Icc_subset_Icc (by linarith) (by linarith)
  have hmem : ∀ t ∈ Icc (0:ℝ) L, u t ∈ (extChartAt I x₀).target :=
    fun t ht => hstay_u t (hsubL ht)
  have hmemM : ∀ t ∈ Icc (-1:ℝ) (L+2), u t ∈ (extChartAt I x₀).target :=
    fun t ht => hstay_u t (hsubM ht)
  -- the geodesic velocity field and the parallel field
  set w' : ℝ → E := fun t => chartGeodesicVectorField cov x₀ (u t, w t) with hw'def
  obtain ⟨Y, hYODE, hYunit, hYorth⟩ :=
    exists_parallel_unit_orthogonal_Ioo (cov := cov) hmet htor hdim hstay_u hu hw
      (a := -1) (b := L+2) (t₀ := 0) hA1 hsubM ⟨by linarith, by linarith⟩ hunit
  -- the parallel condition in the form needed
  have hpenv_eq : ∀ r ∈ Icc (-1:ℝ) (L+2),
      penv (cov := cov) x₀ u w Y r
        = -(christoffelLM cov x₀ ((extChartAt I x₀).symm (u r))
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u r)) (w r))) (Y r) := by
    intro r hr
    rw [penv, christoffelLM_apply (cov := cov) (mem_source_chartCurve (I := I) (hmemM r hr))]
    rfl
  have hY' : ∀ t ∈ Icc (0:ℝ) L, HasDerivAt Y (penv (cov := cov) x₀ u w Y t) t := by
    intro t ht
    exact (hYODE t (hsubLM ht)).congr_deriv (hpenv_eq t (hsubLM ht)).symm
  have hpar : ∀ t ∈ Icc (0:ℝ) L,
      deriv Y t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0 := by
    intro t ht
    have h := (hY' t ht).deriv
    rw [h, penv]
    abel
  have hYev : ∀ t ∈ Icc (0:ℝ) L, deriv Y =ᶠ[𝓝 t] penv (cov := cov) x₀ u w Y := by
    intro t ht
    have htIoo : t ∈ Ioo (-1:ℝ) (L+2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    filter_upwards [isOpen_Ioo.mem_nhds htIoo] with r hr
    have hr' : r ∈ Icc (-1:ℝ) (L+2) := ⟨le_of_lt hr.1, le_of_lt hr.2⟩
    rw [(hYODE r hr').deriv, hpenv_eq r hr']
  -- the test field and its derivatives
  set η : ℝ → E := testField (E := E) L Y with hηdef
  set e : ℝ → E := testFieldDeriv (E := E) L Y with hedef
  set e' : ℝ → E := tfd' (cov := cov) x₀ u w w' Y L with he'def
  have huC : ∀ t ∈ Icc (0:ℝ) L, HasDerivAt u (w t) t := fun t ht => hu t (hsubL ht)
  have hwC : ∀ t ∈ Icc (0:ℝ) L, HasDerivAt w (w' t) t := fun t ht => hw t (hsubL ht)
  have hstayn : ∀ t ∈ Icc (0:ℝ) L, ∀ᶠ r in 𝓝 t, u r ∈ (extChartAt I x₀).target := by
    intro t ht
    exact (huC t ht).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (hmem t ht))
  have hηe : ∀ t ∈ Icc (0:ℝ) L, tfd (cov := cov) x₀ u w Y L t = e t := by
    intro t ht
    rw [hedef, testFieldDeriv, tfd, (hY' t ht).deriv]
  have hη : ∀ t ∈ Icc (0:ℝ) L, HasDerivAt η (e t) t := by
    intro t ht
    refine (hasDerivAt_testField' (cov := cov) (L := L) (hY' t ht)).congr_deriv ?_
    exact hηe t ht
  have he : ∀ t ∈ Icc (0:ℝ) L, HasDerivAt e (e' t) t := by
    intro t ht
    have hpenv := hasDerivAt_penv (cov := cov) (huC t ht) (hY' t ht) (hwC t ht)
      (hmem t ht) (hstayn t ht)
    have hderivY : HasDerivAt (fun r : ℝ => deriv Y r) (penv' (cov := cov) x₀ u w w' Y t) t :=
      (hYev t ht).hasDerivAt_iff.mpr hpenv
    have hdy : deriv Y t = penv (cov := cov) x₀ u w Y t := (hYev t ht).eq_of_nhds
    have h1 := (hasDerivAt_cos_pi L t).smul (hY' t ht)
    have h2 := (hasDerivAt_sin_pi L t).smul hderivY
    have h3 := h1.add h2
    rw [hedef]
    refine h3.congr_deriv ?_
    rw [he'def, hdy]
    simp only [tfd', penv]
    module
  have hYcont : ContinuousOn Y (Icc (0:ℝ) L) :=
    HasDerivAt.continuousOn (fun t ht => hYODE t (hsubLM ht))
  have hw'cont : ContinuousOn w' (Icc (0:ℝ) L) := by
    have hpair : ContinuousOn (fun t : ℝ => (u t, w t)) (Icc (0:ℝ) L) :=
      (HasDerivAt.continuousOn huC).prodMk (HasDerivAt.continuousOn hwC)
    have hmap : MapsTo (fun t : ℝ => (u t, w t)) (Icc (0:ℝ) L)
        ((extChartAt I x₀).target ×ˢ (Set.univ : Set E)) :=
      fun t ht => ⟨hmem t ht, Set.mem_univ _⟩
    have hspray := (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray
      (cov := cov) x₀).continuousOn
    have hcomp := hspray.comp hpair hmap
    have hfun : w' = (chartGeodesicVectorField cov x₀) ∘ (fun t : ℝ => (u t, w t)) := by
      funext t; rfl
    rw [hfun]
    exact hcomp
  have he'cont : ContinuousOn e' (Icc (0:ℝ) L) := by
    rw [he'def]
    exact continuousOn_tfd' (cov := cov) (HasDerivAt.continuousOn huC) (HasDerivAt.continuousOn hwC)
      hw'cont hYcont hmem
  -- the endpoints of the test field
  have hη0 : η 0 = 0 := by
    show Real.sin (Real.pi * (0:ℝ) / L) • Y 0 = 0
    rw [show Real.pi * (0:ℝ) / L = 0 by ring, Real.sin_zero, zero_smul]
  have hηL : η L = 0 := by
    show Real.sin (Real.pi * L / L) • Y L = 0
    rw [show Real.pi * L / L = Real.pi by field_simp, Real.sin_pi, zero_smul]
  -- the geodesic equation in the required form
  have hgeo : ∀ t ∈ Icc (0:ℝ) L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0 := by
    intro t ht
    show chartGeodesicVectorField cov x₀ (u t, w t)
      + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0
    simp only [chartGeodesicVectorField, chrB_apply, neg_add_cancel]
  -- the family target condition
  have hηcontM : ContinuousOn η (Icc (-1:ℝ) (L+2)) := by
    rw [hηdef]
    refine ContinuousOn.smul ?_ ?_
    · fun_prop
    · exact HasDerivAt.continuousOn (fun t ht => hYODE t ht)
  have hucontM : ContinuousOn u (Icc (-1:ℝ) (L+2)) :=
    HasDerivAt.continuousOn (fun t ht => hu t (hsubM ht))
  obtain ⟨δ, hδpos, hδ⟩ := exists_fam_mem_target (x₀ := x₀) hucontM hηcontM hmemM
  have hfam : ∀ s ∈ Icc (-δ) δ, ∀ t ∈ Icc (-1:ℝ) (L+2),
      fam u η s t ∈ (extChartAt I x₀).target := by
    intro s hs t ht
    show u t + s • η t ∈ (extChartAt I x₀).target
    exact hδ s hs t ht
  -- the index-form integral bound
  have hsrc : ∀ t ∈ Icc (0:ℝ) L, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (hmem t ht)
  have hunit' : ∀ t ∈ Icc (0:ℝ) L,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (Y t) = 1 :=
    fun t ht => hYunit t (hsubLM ht)
  have horth : ∀ t ∈ Icc (0:ℝ) L,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0 :=
    fun t ht => hYorth t (hsubLM ht)
  have hwunit' : ∀ t ∈ Icc (0:ℝ) L,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1 := by
    intro t ht
    have hgeo' : ∀ s ∈ Icc (0:ℝ) L,
        w' s + chrB cov x₀ ((extChartAt I x₀).symm (u s)) (w s) (w s) = 0 := hgeo
    have hc := chartGram_const_Icc (cov := cov) hmet hL.le huC hwC hgeo' hmem t ht
    rw [hc]
    exact hunit
  have hint : IntervalIntegrable (fun t : ℝ => indexIntegrand cov x₀ u η w e t) volume 0 L :=
    (continuousOn_indexIntegrand' (cov := cov) htor huC hwC hη he hw'cont he'cont hmem).intervalIntegrable_of_Icc hL.le
  have hInt := indexIntegrand_testField_integral (cov := cov) ‹ContMDiffCovariantDerivative cov ∞›
    hmet htor hpinch x₀ hL hsrc hunit' horth hwunit' hpar hint
  -- the conclusion
  exact le_pi_of_minimising_chart_geodesic (x₀ := x₀) (L := L) (u := u) (η := η) (w := w) (e := e)
    (w' := w') (e' := e') (a₁ := -δ) (a₂ := δ)
    (ha₁ := by linarith [hδpos]) (ha₂ := by linarith [hδpos])
    hmet htor hL huC hwC hη he hw'cont he'cont hη0 hηL hgeo hfam hmem hunit hmin hInt

end

end Submission.BonnetMyers3