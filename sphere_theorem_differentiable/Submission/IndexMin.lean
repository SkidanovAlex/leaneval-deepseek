import Submission.IndexCorner2
import Submission.JacobiTensor
import Submission.RayJacobiTensor
import Submission.GeoChartCurve

set_option backward.isDefEq.respectTransparency.types false

/-!
# No conjugate point in the interior of a minimising geodesic (chart/tensor form)

`Submission.IndexCorner2.eqOn_zero_of_minimising_chart` proves, in the language of the *energy second
variation*, that a Jacobi field along a minimising chart geodesic vanishing at `0` and at an interior
time `t₀` must vanish on `[0,t₀]`.  This file converts that theorem into the form the exponential map
actually uses: **the Jacobi tensor of a minimising chart geodesic is injective.**

Contents:

* `chartCovDeriv_jacobiCol_eventuallyEq_Ioo`, `hasDerivAt_chartCovDeriv_jacobiCol_Ioo`,
  `jacobiEquation_col_Ioo` — the pointwise lemmas of `Submission.JacobiTensor` re-proved for an
  arbitrary *open* interval `Ioo A B` (the originals are tied to `Ioo (-2) 2`, which is too small for
  a minimising geodesic of length `L ≥ 2`);
* `DtDsP_eq_chartCovDeriv_chartCovDeriv` — the bridge identifying the `DtDsP` form of the second
  covariant derivative (the form consumed by `IndexCorner2`) with the two-fold `chartCovDeriv`;
* **`jacobiTensor_injective_of_minimising`** — let `γ t = (extChartAt I x₀).symm (u t)` be a unit-speed
  chart geodesic on `[0,L]` realising the distance between its endpoints, and let `(Y,U)` solve the
  Jacobi system `Y' = U - Γ̂ ∘ Y`, `U' = -Γ̂ ∘ U - R̂ ∘ Y` with `Y 0 = 0`, `U 0 = 1`.  Then `Y t₁` is
  **injective** for every `t₁ ∈ (0,L)`: there is no conjugate point strictly inside a minimising
  geodesic.  (`Submission.JacobiTensor.jacobiTensor_injective` proves the same conclusion for
  `t₁ < π/2` from the curvature bound `sec ≤ 4` via Rauch; this version replaces the curvature bound by
  the *minimising* hypothesis `hmin`, which is the classical `σ ≤ κ` in the tensor form.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartCurv
open Submission.ChartConnection
open Submission.Rauch
open Submission.SecondVariation
open Submission.ChartBounds
open Submission.BonnetMyers
open Submission.JacobiTensor
open Submission.FlowJacobi
open Submission.GlobalBM
open Submission.IndexCorner2
open Submission.IndexCorner
open Submission.GlobalExp
open Submission.GeoChartCurve
open Submission.RayJT

namespace Submission.IndexMin

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- The covariant derivative of a column of a Jacobi system agrees near `t` with the `U`-column. -/
lemma chartCovDeriv_jacobiCol_eventuallyEq_Ioo {x₀ : M} {u w : ℝ → E}
    {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ} {A B : ℝ} (ht : t ∈ Ioo A B)
    (hY : ∀ s ∈ Ioo A B,
      HasDerivAt Y (U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) s) :
    chartCovDeriv cov x₀ u w (fun s => Y s a) =ᶠ[𝓝 t] (fun s => U s a) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact chartCovDeriv_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a) (hY s hs)

/-- The covariant derivative of a column is differentiable, with derivative given by `U'`. -/
lemma hasDerivAt_chartCovDeriv_jacobiCol_Ioo {x₀ : M} {u w : ℝ → E}
    {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ} {A B : ℝ} (ht : t ∈ Ioo A B)
    (hY : ∀ s ∈ Ioo A B,
      HasDerivAt Y (U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) s)
    (hU : ∀ s ∈ Ioo A B, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w s).comp (U s))
      - (curvOp (cov := cov) x₀ u w s).comp (Y s)) s) :
    HasDerivAt (chartCovDeriv cov x₀ u w (fun s => Y s a))
      (((-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t))) a) t := by
  have hev := chartCovDeriv_jacobiCol_eventuallyEq_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
    (Y := Y) (U := U) (a := a) ht hY
  have h := hasDerivAt_jacobiCol_covDeriv (cov := cov) (x₀ := x₀) (u := u) (w := w)
    (a := a) (hU t ht)
  exact h.congr_of_eventuallyEq hev

/-- The chart Jacobi equation for the columns of a Jacobi system, on a general open interval. -/
lemma jacobiEquation_col_Ioo {x₀ : M} {u w : ℝ → E} {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    {A B : ℝ} (ht : t ∈ Ioo A B)
    (hY : ∀ s ∈ Ioo A B,
      HasDerivAt Y (U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) s)
    (hU : ∀ s ∈ Ioo A B, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w s).comp (U s))
      - (curvOp (cov := cov) x₀ u w s).comp (Y s)) s)
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source) :
    chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w (fun s => Y s a)) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) ((Y t) a) (w t) = 0 := by
  have hev := chartCovDeriv_jacobiCol_eventuallyEq_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
    (Y := Y) (U := U) (a := a) ht hY
  have hderiv : deriv (chartCovDeriv cov x₀ u w (fun s => Y s a)) t
      = (((-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t))) a) := by
    rw [Filter.EventuallyEq.deriv_eq hev]
    exact (hasDerivAt_jacobiCol_covDeriv (cov := cov) (x₀ := x₀) (u := u) (w := w)
      (a := a) (hU t ht)).deriv
  have hval : chartCovDeriv cov x₀ u w (fun s => Y s a) t = (U t) a := hev.eq_of_nhds
  show deriv (chartCovDeriv cov x₀ u w (fun s => Y s a)) t
      + (christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)))
          (chartCovDeriv cov x₀ u w (fun s => Y s a) t)
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) ((Y t) a) (w t) = 0
  rw [hderiv, hval]
  simp only [gammaOp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply]
  rw [curvOp_apply (cov := cov) hsrc]
  abel

/-- **`DtDsP` is the two-fold `chartCovDeriv`** when `J'` is the derivative of `J` near `t`. -/
lemma DtDsP_eq_chartCovDeriv_chartCovDeriv (htor : cov.torsion = 0) {x₀ : M} {u w J J' : ℝ → E}
    {t : ℝ} (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source)
    (htgt : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target)
    (hJ : ∀ᶠ s in 𝓝 t, HasDerivAt J (J' s) s) :
    DtDsP cov x₀ u J w J' t
      = chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w J) t := by
  have hev : (fun s : ℝ => covDsP cov x₀ u J w J' 0 s)
      =ᶠ[𝓝 t] chartCovDeriv cov x₀ u w J := by
    filter_upwards [hJ, htgt] with s hs hts
    have hsrcs : (extChartAt I x₀).symm (u s) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) hts
    rw [chartCovDeriv_eq_DtQ (cov := cov) htor x₀ hsrcs hs]
    rfl
  have h1 : deriv (fun s : ℝ => covDsP cov x₀ u J w J' 0 s) t
      = deriv (chartCovDeriv cov x₀ u w J) t := Filter.EventuallyEq.deriv_eq hev
  have h2 : covDsP cov x₀ u J w J' 0 t = chartCovDeriv cov x₀ u w J t := hev.eq_of_nhds
  have hDtDsP : DtDsP cov x₀ u J w J' t
      = deriv (fun s : ℝ => covDsP cov x₀ u J w J' 0 s) t
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (covDsP cov x₀ u J w J' 0 t) (w t) := rfl
  rw [hDtDsP, h1, h2]
  rw [show chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w J) t
      = deriv (chartCovDeriv cov x₀ u w J) t
        + christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
            (chartCovDeriv cov x₀ u w J t) from rfl,
    christoffelLM_apply (cov := cov) hsrc, chrB_apply]

/-- **No conjugate point in the interior of a minimising chart geodesic (Jacobi-tensor form).** -/
theorem jacobiTensor_injective_of_minimising
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {u w : ℝ → E} {L : ℝ} (hL : 0 < L)
    (htgt : ∀ t ∈ Icc (-1 : ℝ) (L + 1), u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Icc (-1 : ℝ) (L + 1), HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc (-1 : ℝ) (L + 1),
      HasDerivAt w (chartGeodesicVectorField cov x₀ (u t, w t)) t)
    (hunit : ∀ t ∈ Icc (0:ℝ) L,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    (hmin : Manifold.riemannianEDist I ((extChartAt I x₀).symm (u 0))
      ((extChartAt I x₀).symm (u L)) = ENNReal.ofReal L)
    {Y U : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Icc (-1 : ℝ) (L + 1),
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Icc (-1 : ℝ) (L + 1),
      HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1)
    {t₁ : ℝ} (ht₁ : 0 < t₁) (ht₁L : t₁ < L) :
    Function.Injective (Y t₁) := by
  intro a b hab
  set c : E := a - b with hcdef
  set J : ℝ → E := fun s => Y s c with hJdef
  set Wq : ℝ → E := fun s => chartGeodesicVectorField cov x₀ (u s, w s) with hWqdef
  set Q : ℝ → E := fun s => (gammaOp (cov := cov) x₀ u w s) ((Y s) c) with hQdef
  set J' : ℝ → E := fun s => (U s) c - Q s with hJ'def
  set zz : ℝ → E := fun s => (-((gammaOp (cov := cov) x₀ u w s).comp (U s))
      - (curvOp (cov := cov) x₀ u w s).comp (Y s)) c with hzzdef
  set QQ : ℝ → E := fun s =>
      dB cov x₀ ((extChartAt I x₀).symm (u s)) (w s) (w s) (J s)
      + chrB cov x₀ ((extChartAt I x₀).symm (u s)) (Wq s) (J s)
      + chrB cov x₀ ((extChartAt I x₀).symm (u s)) (w s) (J' s) with hQQdef
  set J'' : ℝ → E := fun s => zz s - QQ s with hJ''def
  have hmem : ∀ t ∈ Icc (0:ℝ) L, t ∈ Icc (-1 : ℝ) (L + 1) :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmemIoo : ∀ t ∈ Icc (0:ℝ) L, t ∈ Ioo (-1 : ℝ) (L + 1) :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- differentiability of `J`
  have hJdRaw : ∀ t ∈ Ioo (-1 : ℝ) (L + 1), HasDerivAt J (J' t) t := by
    intro t ht
    have h := hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := c)
      (hY t ⟨ht.1.le, ht.2.le⟩)
    simpa only [hJdef, hJ'def, hQdef] using h
  have hJd : ∀ t ∈ Icc (0:ℝ) L, HasDerivAt J (J' t) t := fun t ht => hJdRaw t (hmemIoo t ht)
  -- differentiability of the `U`-column and of `Q`
  have hUcd : ∀ t ∈ Ioo (-1 : ℝ) (L + 1), HasDerivAt (fun s : ℝ => U s c) (zz t) t := by
    intro t ht
    have h := hasDerivAt_jacobiCol_covDeriv (cov := cov) (x₀ := x₀) (u := u) (w := w)
      (a := c) (hU t ⟨ht.1.le, ht.2.le⟩)
    simpa only [hzzdef] using h
  have hQd : ∀ t ∈ Ioo (-1 : ℝ) (L + 1), HasDerivAt Q (QQ t) t := by
    intro t ht
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      (hu t ⟨ht.1.le, ht.2.le⟩).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (htgt t ⟨ht.1.le, ht.2.le⟩))
    have h := hasDerivAt_chrB_fam_t (cov := cov) (x₀ := x₀) (u := u) (η := J) (w := w)
      (e := J') (w' := Wq) (t₀ := t) (hu t ⟨ht.1.le, ht.2.le⟩) (hw t ⟨ht.1.le, ht.2.le⟩)
      (hJdRaw t ht) (htgt t ⟨ht.1.le, ht.2.le⟩) hstay
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hstay] with s hs
    have hsrcs : (extChartAt I x₀).symm (u s) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) hs
    simp only [hQdef, hJdef]
    rw [gammaOp_apply (cov := cov) (x₀ := x₀) (u := u) (w := w) (t := s) hsrcs,
      ← chrB_comm htor hsrcs ((Y s) c) (w s), chrB_apply]
  have hIooY : ∀ t ∈ Ioo (-1 : ℝ) (L + 1),
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t :=
    fun t ht => hY t ⟨ht.1.le, ht.2.le⟩
  have hIooU : ∀ t ∈ Ioo (-1 : ℝ) (L + 1),
      HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t :=
    fun t ht => hU t ⟨ht.1.le, ht.2.le⟩
  have hJ'd : ∀ t ∈ Ioo (-1 : ℝ) (L + 1), HasDerivAt J' (J'' t) t := by
    intro t ht
    have h : HasDerivAt ((fun s : ℝ => U s c) - Q) (zz t - QQ t) t :=
      (hUcd t ht).sub (hQd t ht)
    have hh : ((fun s : ℝ => U s c) - Q) = fun s : ℝ => U s c - Q s := by
      funext s; rfl
    rw [hh] at h
    have h1 : J' = fun s : ℝ => U s c - Q s := by rw [hJ'def]
    have h2 : J'' t = zz t - QQ t := by rw [hJ''def]
    rw [h1, h2]
    exact h
  -- continuities
  have huIcc : ContinuousOn u (Icc (0:ℝ) L) :=
    HasDerivAt.continuousOn (fun t ht => hu t (hmem t ht))
  have hwIcc : ContinuousOn w (Icc (0:ℝ) L) :=
    HasDerivAt.continuousOn (fun t ht => hw t (hmem t ht))
  have hWqIcc : ContinuousOn Wq (Icc (0:ℝ) L) := by
    have hspray := Submission.GeodesicGlobal.contDiffOn_chartSpray' (cov := cov) x₀
    have huw : ContinuousOn (fun s : ℝ => (u s, w s)) (Icc (0:ℝ) L) := huIcc.prodMk hwIcc
    have hc := (ContDiffOn.continuousOn hspray).comp huw
      (fun s hs => ⟨htgt s (hmem s hs), Set.mem_univ _⟩)
    refine hc.congr fun s _ => ?_
    rw [hWqdef]
    rfl
  have hJc : ContinuousOn J (Icc (0:ℝ) L) := HasDerivAt.continuousOn hJd
  have hYc : ContinuousOn (fun s : ℝ => Y s c) (Icc (0:ℝ) L) :=
    HasDerivAt.continuousOn (fun t ht =>
      hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := c) (hY t (hmem t ht)))
  have hUc' : ContinuousOn (fun s : ℝ => U s c) (Icc (0:ℝ) L) :=
    HasDerivAt.continuousOn (fun t ht => hUcd t (hmemIoo t ht))
  have hγc : ContinuousOn (fun s : ℝ => (extChartAt I x₀).symm (u s)) (Icc (0:ℝ) L) :=
    continuousOn_chartCurve (I := I) huIcc (fun t ht => htgt t (hmem t ht))
  have hmem' : ∀ t ∈ Icc (0:ℝ) L, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (htgt t (hmem t ht))
  have hQcont : ContinuousOn Q (Icc (0:ℝ) L) := by
    have hcb := continuousOn_chrB_curve (cov := cov) (x₀ := x₀) hγc hYc hwIcc hmem'
    refine hcb.congr fun s hs => ?_
    have hsrcs : (extChartAt I x₀).symm (u s) ∈ (chartAt H x₀).source := hmem' s hs
    simp only [hQdef]
    rw [gammaOp_apply (cov := cov) (x₀ := x₀) (u := u) (w := w) (t := s) hsrcs, chrB_apply]
  have hJ'cont : ContinuousOn J' (Icc (0:ℝ) L) := by
    have h : ContinuousOn ((fun s : ℝ => U s c) - Q) (Icc (0:ℝ) L) := hUc'.sub hQcont
    have hh : ((fun s : ℝ => U s c) - Q) = fun s : ℝ => U s c - Q s := by
      funext s; rfl
    rw [hh] at h
    rw [hJ'def]
    exact h
  have hGop : ContinuousOn (fun s : ℝ => gammaOp (cov := cov) x₀ u w s) (Icc (0:ℝ) L) :=
    continuousOn_gammaOp_of_cont (cov := cov) htor huIcc hwIcc (fun t ht => htgt t (hmem t ht))
  have hRop : ContinuousOn (fun s : ℝ => curvOp (cov := cov) x₀ u w s) (Icc (0:ℝ) L) :=
    continuousOn_curvOp (cov := cov) huIcc hwIcc (fun t ht => htgt t (hmem t ht))
  have hzzcont : ContinuousOn zz (Icc (0:ℝ) L) := by
    have h1 : ContinuousOn (fun s : ℝ => (gammaOp (cov := cov) x₀ u w s) (U s c))
        (Icc (0:ℝ) L) := hGop.clm_apply hUc'
    have h2 : ContinuousOn (fun s : ℝ => (curvOp (cov := cov) x₀ u w s) (Y s c))
        (Icc (0:ℝ) L) := hRop.clm_apply hYc
    have h3 := h1.neg.sub h2
    rw [hzzdef]
    exact h3
  have hQQcont : ContinuousOn QQ (Icc (0:ℝ) L) := by
    have h1 : ContinuousOn (fun s : ℝ =>
        dB cov x₀ ((extChartAt I x₀).symm (u s)) (w s) (w s) (J s)) (Icc (0:ℝ) L) :=
      continuousOn_dB_curve (cov := cov) (x₀ := x₀) hγc hwIcc hwIcc hJc hmem'
    have h2 : ContinuousOn (fun s : ℝ =>
        chrB cov x₀ ((extChartAt I x₀).symm (u s)) (Wq s) (J s)) (Icc (0:ℝ) L) :=
      continuousOn_chrB_curve (cov := cov) (x₀ := x₀) hγc hWqIcc hJc hmem'
    have h3 : ContinuousOn (fun s : ℝ =>
        chrB cov x₀ ((extChartAt I x₀).symm (u s)) (w s) (J' s)) (Icc (0:ℝ) L) :=
      continuousOn_chrB_curve (cov := cov) (x₀ := x₀) hγc hwIcc hJ'cont hmem'
    have h4 := (h1.add h2).add h3
    rw [hQQdef]
    exact h4
  have hJ''cont : ContinuousOn J'' (Icc (0:ℝ) L) := by
    have h : ContinuousOn ((zz : ℝ → E) - QQ) (Icc (0:ℝ) L) := hzzcont.sub hQQcont
    have hh : ((zz : ℝ → E) - QQ) = fun s : ℝ => zz s - QQ s := by
      funext s; rfl
    rw [hh] at h
    rw [hJ''def]
    exact h
  -- the geodesic equation in the chart and the Jacobi equation
  have hgeo : ∀ t ∈ Icc (0:ℝ) L,
      Wq t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0 := by
    intro t ht
    rw [hWqdef]
    simp only [chartGeodesicVectorField, chrB_apply]
    abel
  have hjac : ∀ t ∈ Icc (0:ℝ) L,
      DtDsP cov x₀ u J w J' t
        + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0 := by
    intro t ht
    have ht' : t ∈ Ioo (-1 : ℝ) (L + 1) := hmemIoo t ht
    have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source := hmem' t ht
    have hevJ : ∀ᶠ s in 𝓝 t, HasDerivAt J (J' s) s :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht') (fun s hs => hJdRaw s hs)
    have hevtgt : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      (hu t ⟨ht'.1.le, ht'.2.le⟩).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (htgt t ⟨ht'.1.le, ht'.2.le⟩))
    have hbridge := DtDsP_eq_chartCovDeriv_chartCovDeriv (cov := cov) htor (x₀ := x₀)
      (u := u) (w := w) (J := J) (J' := J') (t := t) hsrc hevtgt hevJ
    have hcol := jacobiEquation_col_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
      (Y := Y) (U := U) (a := c) ht' hIooY hIooU hsrc
    rw [hbridge]
    simpa only [hJdef] using hcol
  have hJ0 : J 0 = 0 := by
    show (Y 0) c = 0
    rw [hY0]
    simp
  have hJt : J t₁ = 0 := by
    show (Y t₁) c = 0
    rw [hcdef, map_sub, hab, sub_self]
  have hzero : ∀ t ∈ Icc (0:ℝ) t₁, J t = 0 :=
    eqOn_zero_of_minimising_chart (cov := cov) (J := J) (J' := J') (J'' := J'') (t₀ := t₁)
      hmet htor x₀ hL
      (fun t ht => hu t (hmem t ht))
      (fun t ht => hw t (hmem t ht))
      hWqIcc
      (fun t ht => htgt t (hmem t ht))
      hgeo hunit hmin
      ht₁ ht₁L
      (fun t ht => hJd t ht)
      hJ'cont
      (fun t ht => hJ'd t (hmemIoo t ht))
      hJ''cont
      hjac hJ0 hJt
  -- the derivative of `J` at `0` is `c ≠ 0`, contradicting `J ≡ 0` on `[0,t₁]`
  have hder0 : HasDerivAt J c 0 := by
    have h := hJdRaw 0 ⟨by norm_num, by linarith⟩
    refine h.congr_deriv ?_
    show (U 0) c - Q 0 = c
    simp [hQdef, hU0, hY0]
  have hslope : Filter.Tendsto (fun t : ℝ => t⁻¹ • (J t - J 0)) (𝓝[>] (0:ℝ)) (𝓝 c) := by
    simpa only [zero_add] using hder0.tendsto_slope_zero_right
  have hzero_slope : (fun t : ℝ => t⁻¹ • (J t - J 0)) =ᶠ[𝓝[>] (0:ℝ)] (fun _ => (0 : E)) := by
    filter_upwards [Ioo_mem_nhdsGT ht₁] with t ht
    rw [hzero t ⟨ht.1.le, ht.2.le⟩, hJ0, sub_self, smul_zero]
  have h0lim : Filter.Tendsto (fun t : ℝ => t⁻¹ • (J t - J 0)) (𝓝[>] (0:ℝ)) (𝓝 (0 : E)) :=
    Filter.Tendsto.congr' hzero_slope.symm tendsto_const_nhds
  have hc0 : c = 0 := tendsto_nhds_unique hslope h0lim
  exact sub_eq_zero.mp (by rw [← hcdef]; exact hc0)


section GExpRay

variable [Nontrivial E] [CompactSpace M]

theorem jacobiTensor_GExp_injective_of_minimising
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {p : M} {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {L : ℝ} (hL : 0 < L)
    (hsrc : ∀ s ∈ Icc (-1 : ℝ) (L + 1),
      GExp (cov := cov) hmet p (s • ξ) ∈ (chartAt H x₀).source)
    (hmin : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (L • ξ)) = ENNReal.ofReal L)
    {Y U : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Icc (-1 : ℝ) (L + 1), HasDerivAt Y (U t
      - (gammaOp (cov := cov) x₀ (rayU hmet x₀ p ξ) (rayW hmet x₀ p ξ) t).comp (Y t)) t)
    (hU : ∀ t ∈ Icc (-1 : ℝ) (L + 1), HasDerivAt U
      (-((gammaOp (cov := cov) x₀ (rayU hmet x₀ p ξ) (rayW hmet x₀ p ξ) t).comp (U t))
        - (curvOp (cov := cov) x₀ (rayU hmet x₀ p ξ) (rayW hmet x₀ p ξ) t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1) :
    ∀ t₁ ∈ Ioo (0:ℝ) L, Function.Injective (Y t₁) := by
  have hξ0 : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  intro t₁ ht₁
  refine jacobiTensor_injective_of_minimising (cov := cov)
    (u := rayU hmet x₀ p ξ) (w := rayW hmet x₀ p ξ) hmet htor x₀ hL ?_ ?_ ?_ ?_ ?_ hY hU hY0 hU0
    ht₁.1 ht₁.2
  · intro t ht
    exact (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hsrc t ht)
  · intro t ht
    exact hasDerivAt_chartCurve_GExp (cov := cov) hmet x₀ hξ0 t (hsrc t ht)
  · intro t ht
    exact hasDerivAt_deriv_chartCurve_GExp (cov := cov) hmet x₀ hξ0 t (hsrc t ht)
  · intro t ht
    exact chartGram_chartCurve_GExp (cov := cov) hmet x₀ hξ t
      (hsrc t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  · have h0mem : (0:ℝ) ∈ Icc (-1 : ℝ) (L + 1) := ⟨by norm_num, by linarith⟩
    have hLmem : L ∈ Icc (-1 : ℝ) (L + 1) := ⟨by linarith, by linarith⟩
    have hp : p ∈ (extChartAt I x₀).source := by
      have h1 := hsrc 0 h0mem
      rw [zero_smul, GExp_zero] at h1
      rwa [extChartAt_source]
    have hq : GExp (cov := cov) hmet p (L • ξ) ∈ (extChartAt I x₀).source := by
      have h1 := hsrc L hLmem
      rwa [extChartAt_source]
    have e0 : rayU hmet x₀ p ξ 0 = (extChartAt I x₀) p := by
      simp only [rayU, zero_smul, GExp_zero]
    have eL : rayU hmet x₀ p ξ L = (extChartAt I x₀) (GExp (cov := cov) hmet p (L • ξ)) := rfl
    rw [e0, eL, (extChartAt I x₀).left_inv hp, (extChartAt I x₀).left_inv hq]
    exact hmin

end GExpRay

end

end Submission.IndexMin
