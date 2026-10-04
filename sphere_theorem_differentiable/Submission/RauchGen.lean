import Submission.RauchUpper
import Submission.JacobiGen
import Submission.RauchLocal
import Submission.ChartBounds

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The upper Rauch comparison theorem on an arbitrary chart interval

`Submission/RauchUpper.lean` develops the Riccati/shape-operator form of Rauch's upper comparison
theorem for a chart geodesic defined on the **fixed** interval `Ioo (-2) 2`.  For the comparison
theorems along a (long) geodesic — and for the pointwise bound on the differential of the
exponential map — the same chain is needed on an **arbitrary** interval `Ioo A B` (`A < 0 < B`)
with the invertibility of the Jacobi tensor supplied as a hypothesis (`Window`).

Everything in this file is literally the same proof as in `Submission/RauchUpper.lean` with
`Ioo (-2) 2` replaced by `Ioo A B`, generalising `HasChartGeodesic` in the same way that
`Submission/JacobiGen.lean` generalises `Submission/Jacobi.lean`.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Curvature
open Submission.CurvatureVec
open Submission.Rauch
open Submission.ChartBounds
open Submission.JacobiVec
open Submission.JacobiTensor
open Submission.CurvatureSym
open Submission.Gauss
open Submission.JacobiGen
open Submission.IndexForm
open Submission.ConjPoint
open Submission.RauchGlobal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.RauchGen

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **A chart geodesic on an arbitrary interval.**  Same clauses as `HasChartGeodesic`, but the
geodesic equation and the chart condition are required only on `Ioo A B`. -/
def HasChartGeodesicOn (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x : M)
    (q : M) (v : TangentSpace I q) (u w : ℝ → E) (A B : ℝ) : Prop :=
  u 0 = (extChartAt I x) q ∧
    w 0 = (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ q v ∧
    (∀ t ∈ Ioo A B, u t ∈ (extChartAt I x).target) ∧
    (∀ t ∈ Ioo A B, HasDerivAt u (w t) t) ∧
    (∀ t ∈ Ioo A B, HasDerivAt w (chartGeodesicVectorField cov x (u t, w t)) t)

/-- **A chart geodesic on an interval can be rescaled.**  If `(u, w)` solves the chart geodesic
equation on `Ioo A B` with velocity `v`, then `s ↦ (u (r s), r • w (r s))` solves it on
`Ioo (A/r) (B/r)` with velocity `r • v` (this is the homogeneity of the spray,
`chartGeodesicVectorField_smul`). -/
theorem HasChartGeodesicOn.const_smul {x₀ q : M} {v : E} {u w : ℝ → E} {A B : ℝ} {r : ℝ}
    (hr : 0 < r) (h : HasChartGeodesicOn cov x₀ q v u w A B) :
    HasChartGeodesicOn cov x₀ q (r • v) (fun s => u (r * s)) (fun s => r • w (r * s))
      (A / r) (B / r) := by
  have key : ∀ {s : ℝ}, s ∈ Ioo (A / r) (B / r) → r * s ∈ Ioo A B := by
    intro s hs
    refine ⟨?_, ?_⟩
    · have h1 : A < r * s := by
        have := (div_lt_iff₀ hr).mp hs.1
        rwa [mul_comm] at this
      exact h1
    · have h2 : r * s < B := by
        have := (lt_div_iff₀ hr).mp hs.2
        rwa [mul_comm] at this
      exact h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show u (r * 0) = (extChartAt I x₀) q
    rw [mul_zero]; exact h.1
  · show r • w (r * 0)
      = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ q (r • v)
    rw [mul_zero, h.2.1, map_smul]
  · intro s hs
    show u (r * s) ∈ (extChartAt I x₀).target
    exact h.2.2.1 _ (key hs)
  · intro s hs
    show HasDerivAt (fun s : ℝ => u (r * s)) (r • w (r * s)) s
    have hφ : HasDerivAt (fun s : ℝ => r * s) r s := by
      simpa using (hasDerivAt_id s).const_mul r
    have h2 := (h.2.2.2.1 (r * s) (key hs)).scomp s hφ
    simpa [Function.comp_def] using h2
  · intro s hs
    show HasDerivAt (fun s : ℝ => r • w (r * s))
      (chartGeodesicVectorField cov x₀ (u (r * s), r • w (r * s))) s
    have hφ : HasDerivAt (fun s : ℝ => r * s) r s := by
      simpa using (hasDerivAt_id s).const_mul r
    have h2 : HasDerivAt (fun s : ℝ => w (r * s))
        (r • chartGeodesicVectorField cov x₀ (u (r * s), w (r * s))) s := by
      have h3 := (h.2.2.2.2 (r * s) (key hs)).scomp s hφ
      simpa [Function.comp_def] using h3
    have h4 := h2.const_smul r
    refine h4.congr_deriv ?_
    rw [chartGeodesicVectorField_smul cov x₀ r (u (r * s), w (r * s))
      (h.2.2.1 (r * s) (key hs)), smul_smul, pow_two]

/-- The data of the Rauch comparison chapter on an arbitrary interval: a unit-speed chart geodesic
on `Ioo A B` together with a Jacobi system `(Y, U)` along it. -/

structure JData (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M) (q : M)
    (v : E) (u w : ℝ → E) (A B : ℝ) where
  hA : A < 0
  hB : 0 < B
  htor : cov.torsion = 0
  hmet : IsMetricCompatible cov
  hpinch : QuarterPinched cov
  hgeo : HasChartGeodesicOn cov x₀ q v u w A B
  hunit : ∀ t ∈ Ioo A B,
    chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1
  Y : ℝ → E →L[ℝ] E
  U : ℝ → E →L[ℝ] E
  hY : ∀ t ∈ Ioo A B,
    HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t
  hU : ∀ t ∈ Ioo A B, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
    - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t
  hY0 : Y 0 = 0
  hU0 : U 0 = 1

namespace JData

variable [ContMDiffCovariantDerivative cov ∞] {x₀ q : M} {v : E} {u w : ℝ → E} {A B : ℝ}

/-! ## Interval versions of the Jacobi-column lemmas -/

/-- Continuity of the Christoffel operator along a solution of the chart equation on `Ioo A B`. -/
lemma continuousOn_gammaOp_Ioo (D : JData cov x₀ q v u w A B) :
    ContinuousOn (gammaOp (cov := cov) x₀ u w) (Ioo A B) :=
  Submission.JacobiGen.continuousOn_christoffelLM_along_Ioo (cov := cov) D.htor
    (fun t ht => D.hgeo.2.2.1 t ht) (fun t ht => D.hgeo.2.2.2.1 t ht)
    (fun t ht => D.hgeo.2.2.2.2 t ht)

/-- The derivative of a column of a solution of the Jacobi system. -/
lemma hasDerivAt_jacobiCol_Ioo {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (hY : HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t) :
    HasDerivAt (fun s => Y s a) ((U t) a - (gammaOp (cov := cov) x₀ u w t) ((Y t) a)) t := by
  have h := hY.clm_apply (hasDerivAt_const (c := a) (x := t))
  simpa using h

/-- The covariant derivative of a column of a solution of the Jacobi system is the corresponding
column of `U`. -/
lemma chartCovDeriv_jacobiCol_Ioo {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (hY : HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t) :
    chartCovDeriv cov x₀ u w (fun s => Y s a) t = (U t) a := by
  have h := hasDerivAt_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a) hY
  simp only [chartCovDeriv]
  rw [h.deriv]
  simp only [gammaOp]
  abel

/-- The covariant derivative of a column, as a function, agrees near `t` with the corresponding
column of `U`. -/
lemma chartCovDeriv_jacobiCol_eventuallyEq_Ioo {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (ht : t ∈ Ioo A B)
    (hY : ∀ s ∈ Ioo A B, HasDerivAt Y (U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) s) :
    chartCovDeriv cov x₀ u w (fun s => Y s a) =ᶠ[𝓝 t] (fun s => U s a) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact chartCovDeriv_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a) (hY s hs)

/-- The derivative of the covariant derivative of a column. -/
lemma hasDerivAt_jacobiCol_covDeriv_Ioo {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (hU : HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
      - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t) :
    HasDerivAt (fun s => U s a)
      (((-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t))) a) t := by
  have h := hU.clm_apply (hasDerivAt_const (c := a) (x := t))
  simpa using h

/-- The covariant derivative of a column is differentiable with derivative given by `U' a`. -/
lemma hasDerivAt_chartCovDeriv_jacobiCol_Ioo {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (ht : t ∈ Ioo A B)
    (hY : ∀ s ∈ Ioo A B, HasDerivAt Y (U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) s)
    (hU : ∀ s ∈ Ioo A B, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w s).comp (U s))
      - (curvOp (cov := cov) x₀ u w s).comp (Y s)) s) :
    HasDerivAt (chartCovDeriv cov x₀ u w (fun s => Y s a))
      (((-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t))) a) t := by
  have hev := chartCovDeriv_jacobiCol_eventuallyEq_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
    (Y := Y) (U := U) (a := a) ht hY
  have h := hasDerivAt_jacobiCol_covDeriv_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
    (a := a) (hU t ht)
  exact h.congr_of_eventuallyEq hev

/-- **The chart Jacobi equation for the columns of a solution of the Jacobi system.** -/
lemma jacobiEquation_col_Ioo {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (ht : t ∈ Ioo A B)
    (hY : ∀ s ∈ Ioo A B, HasDerivAt Y (U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) s)
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
    exact (hasDerivAt_jacobiCol_covDeriv_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
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

/-! ## The covariance derivative of the velocity vanishes -/

/-- The covariant derivative of the velocity field of a solution of the chart equation vanishes. -/
lemma chartCovDeriv_geodesic_Ioo {u w : ℝ → E}
    (hstay : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Ioo A B, HasDerivAt w (chartGeodesicVectorField cov x₀ (u t, w t)) t) :
    ∀ t ∈ Ioo A B, chartCovDeriv cov x₀ u w w t = 0 :=
  fun t ht => chartCovDeriv_eq_zero_of_hasDerivAt (cov := cov)
    (Submission.JacobiGen.hasDerivAt_velocity_Ioo (cov := cov) hu hw hstay t ht)


/-! ## The Wronskian identity on a general interval -/

/-- The covariant derivative of `s ↦ U s a` (constant `a`) is `-Rop (Y t a)`. -/
lemma chartCovDeriv_U_const_Ioo {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (hU : HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
      - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t) :
    chartCovDeriv cov x₀ u w (fun s => U s a) t
      = -((curvOp (cov := cov) x₀ u w t) ((Y t) a)) := by
  have h := hasDerivAt_jacobiCol_covDeriv_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
    (a := a) hU
  simp only [chartCovDeriv]
  rw [h.deriv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, gammaOp]
  abel

/-- **The Wronskian identity** on a general interval: along a unit-speed chart geodesic with
Jacobi system `(Y, U)`, `⟨U t a, Y t b⟩ = ⟨Y t a, U t b⟩`. -/
theorem wronskian_eq_zero_Ioo (D : JData cov x₀ q v u w A B)
    {a b : E} {t : ℝ} (ht : t ∈ Ioo A B) :
    chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) ((D.U t) a) ((D.Y t) b)
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) ((D.Y t) a) ((D.U t) b) := by
  set F : ℝ → ℝ := fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
    ((D.U s) a) ((D.Y s) b)
    - chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((D.Y s) a) ((D.U s) b)
    with hFdef
  have hderiv : ∀ s ∈ Ioo A B, HasDerivAt F 0 s := by
    intro s hs
    have hutgt : u s ∈ (extChartAt I x₀).target := D.hgeo.2.2.1 s hs
    have hstay : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) fun r hr => D.hgeo.2.2.1 r hr
    have hUa : HasDerivAt (fun r => D.U r a) (deriv (fun r => D.U r a) s) s := by
      have hh := hasDerivAt_jacobiCol_covDeriv_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
        (a := a) (D.hU s hs)
      rw [hh.deriv]; exact hh
    have hYb : HasDerivAt (fun r => D.Y r b) (deriv (fun r => D.Y r b) s) s := by
      have hh := hasDerivAt_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := b)
        (D.hY s hs)
      rw [hh.deriv]; exact hh
    have hYa : HasDerivAt (fun r => D.Y r a) (deriv (fun r => D.Y r a) s) s := by
      have hh := hasDerivAt_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a)
        (D.hY s hs)
      rw [hh.deriv]; exact hh
    have hUb : HasDerivAt (fun r => D.U r b) (deriv (fun r => D.U r b) s) s := by
      have hh := hasDerivAt_jacobiCol_covDeriv_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
        (a := b) (D.hU s hs)
      rw [hh.deriv]; exact hh
    have h1 := hasDerivAt_chartGram_chartCovDeriv (cov := cov) D.hmet x₀
      (D.hgeo.2.2.2.1 s hs) hutgt hstay hUa hYb
    have h2 := hasDerivAt_chartGram_chartCovDeriv (cov := cov) D.hmet x₀
      (D.hgeo.2.2.2.1 s hs) hutgt hstay hYa hUb
    have hmain := h1.sub h2
    have hD1 : chartCovDeriv cov x₀ u w (fun r => D.U r a) s
        = -((curvOp (cov := cov) x₀ u w s) ((D.Y s) a)) :=
      chartCovDeriv_U_const_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (D.hU s hs)
    have hD2 : chartCovDeriv cov x₀ u w (fun r => D.Y r b) s = (D.U s) b :=
      chartCovDeriv_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := b) (D.hY s hs)
    have hD3 : chartCovDeriv cov x₀ u w (fun r => D.Y r a) s = (D.U s) a :=
      chartCovDeriv_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a) (D.hY s hs)
    have hD4 : chartCovDeriv cov x₀ u w (fun r => D.U r b) s
        = -((curvOp (cov := cov) x₀ u w s) ((D.Y s) b)) :=
      chartCovDeriv_U_const_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (D.hU s hs)
    rw [hD1, hD2, hD3, hD4] at hmain
    have hadj : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        ((curvOp (cov := cov) x₀ u w s) ((D.Y s) a)) ((D.Y s) b)
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((D.Y s) a)
            ((curvOp (cov := cov) x₀ u w s) ((D.Y s) b)) := by
      rw [curvOp_apply (cov := cov) (mem_source_chartCurve (I := I) hutgt),
        curvOp_apply (cov := cov) (mem_source_chartCurve (I := I) hutgt)]
      exact chartCurv_self_adjoint (cov := cov) (hcov := ‹ContMDiffCovariantDerivative cov ∞›)
        D.htor D.hmet x₀ (mem_source_chartCurve (I := I) hutgt) ((D.Y s) a) (w s) ((D.Y s) b)
    have hval0 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
          (-((curvOp (cov := cov) x₀ u w s) ((D.Y s) a))) ((D.Y s) b)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((D.U s) a) ((D.U s) b)
        - (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((D.U s) a) ((D.U s) b)
          + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((D.Y s) a)
              (-((curvOp (cov := cov) x₀ u w s) ((D.Y s) b)))) = 0 := by
      have hneg_snd : ∀ x : E, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
          ((D.Y s) a) (-x)
          = -chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((D.Y s) a) x := by
        intro x
        rw [chartGram_comm, chartGram_neg_fst, chartGram_comm]
      rw [chartGram_neg_fst, hneg_snd, hadj]
      ring
    exact hmain.congr_deriv hval0
  have hsub : ∀ x ∈ Icc (min 0 t) (max 0 t), x ∈ Ioo A B := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_min D.hA ht.1) hx.1,
      lt_of_le_of_lt hx.2 (max_lt D.hB ht.2)⟩
  have hconst := Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc min_le_max
    (fun x hx => hderiv x (hsub x hx))
  have hFt : F t = F (min 0 t) := hconst t ⟨min_le_right _ _, le_max_right _ _⟩
  have hF0 : F 0 = F (min 0 t) := hconst 0 ⟨min_le_left _ _, le_max_left _ _⟩
  have hFz : F 0 = 0 := by
    simp only [hFdef, D.hY0, D.hU0, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.one_apply]
    rw [chartGram_zero_snd, chartGram_zero_fst]
    ring
  have hFt0 : F t = 0 := by rw [hFt, ← hF0]; exact hFz
  exact sub_eq_zero.mp hFt0


/-! ## The shape operator, the Riccati equation and Rauch's comparison on `Ioo A B` -/

/-- A time window `(0, T)` on which the Jacobi tensor is invertible. -/
structure Window (D : JData cov x₀ q v u w A B) where
  T : ℝ
  hT : 0 < T
  hTB : T < B
  hTpi : T < Real.pi
  hYinv : ∀ s ∈ Ioo 0 T, (D.Y s).IsInvertible

namespace Window

variable {D : JData cov x₀ q v u w A B}

lemma mem (W : Window D) {t : ℝ} (ht : t ∈ Ioo 0 W.T) : t ∈ Ioo A B :=
  ⟨by linarith [D.hA, ht.1], by linarith [W.hTB, ht.2]⟩

lemma lt_pi (W : Window D) : W.T < Real.pi := W.hTpi

end Window

/-- `(Y t)⁻¹ (Y t x) = x`, pointwise form. -/
theorem inverse_apply_Y_gen (D : JData cov x₀ q v u w A B) {t : ℝ}
    (h : (D.Y t).IsInvertible) (x : E) :
    (D.Y t).inverse (D.Y t x) = x :=
  ContinuousLinearMap.IsInvertible.inverse_apply_self h x

/-- `Y t ((Y t)⁻¹ x) = x`, pointwise form. -/
theorem Y_apply_inverse_gen (D : JData cov x₀ q v u w A B) {t : ℝ}
    (h : (D.Y t).IsInvertible) (x : E) :
    D.Y t ((D.Y t).inverse x) = x :=
  ContinuousLinearMap.IsInvertible.self_apply_inverse h x

/-- **Difference formula for the inverse**, pointwise form. -/
theorem inverse_diff_gen (D : JData cov x₀ q v u w A B) {s t : ℝ}
    (hs : (D.Y s).IsInvertible) (ht : (D.Y t).IsInvertible) :
    (D.Y s).inverse - (D.Y t).inverse
      = -(((D.Y s).inverse).comp ((D.Y s - D.Y t).comp ((D.Y t).inverse))) := by
  ext x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, map_sub]
  rw [Y_apply_inverse_gen D ht x, inverse_apply_Y_gen D hs ((D.Y t).inverse x)]
  abel

/-- **Continuity of the inverse** on a general window. -/
theorem tendsto_inverse_gen (D : JData cov x₀ q v u w A B) (W : Window D) {t : ℝ}
    (ht : t ∈ Ioo 0 W.T) :
    Tendsto (fun s : ℝ => (D.Y s).inverse) (𝓝 t) (𝓝 ((D.Y t).inverse)) := by
  have ht2 : t ∈ Ioo A B := W.mem ht
  have hYt : Tendsto D.Y (𝓝 t) (𝓝 (D.Y t)) := (D.hY t ht2).continuousAt
  have hdtend : Tendsto (fun s : ℝ => ‖D.Y s - D.Y t‖) (𝓝 t) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => D.Y s - D.Y t) (𝓝 t) (𝓝 (0 : E →L[ℝ] E)) := by
      have hc : Tendsto (fun _ : ℝ => D.Y t) (𝓝 t) (𝓝 (D.Y t)) := tendsto_const_nhds
      have h2 := hYt.sub hc
      simpa using h2
    simpa using h1.norm
  have hevint : ∀ᶠ s : ℝ in 𝓝 t, s ∈ Ioo 0 W.T := isOpen_Ioo.mem_nhds ht
  have hevsmall : ∀ᶠ s : ℝ in 𝓝 t, ‖D.Y s - D.Y t‖ * ‖(D.Y t).inverse‖ ≤ 1 / 2 := by
    have h2 : Tendsto (fun s : ℝ => ‖D.Y s - D.Y t‖ * ‖(D.Y t).inverse‖) (𝓝 t) (𝓝 0) := by
      simpa using hdtend.mul_const (‖(D.Y t).inverse‖)
    exact h2.eventually (Iic_mem_nhds (by norm_num : ((0 : ℝ) < 1 / 2)))
  have hnorm_le : ∀ {s : ℝ}, s ∈ Ioo 0 W.T →
      ‖(D.Y s).inverse - (D.Y t).inverse‖
        ≤ ‖(D.Y s).inverse‖ * ‖D.Y s - D.Y t‖ * ‖(D.Y t).inverse‖ := by
    intro s hs
    rw [inverse_diff_gen D (W.hYinv s hs) (W.hYinv t ht), norm_neg]
    refine le_trans (ContinuousLinearMap.opNorm_comp_le
      (h := (D.Y s).inverse) ((D.Y s - D.Y t).comp ((D.Y t).inverse))) ?_
    rw [mul_assoc]
    gcongr
    exact ContinuousLinearMap.opNorm_comp_le (h := D.Y s - D.Y t) ((D.Y t).inverse)
  have hbd : ∀ᶠ s : ℝ in 𝓝 t, ‖(D.Y s).inverse‖ ≤ 2 * ‖(D.Y t).inverse‖ := by
    filter_upwards [hevint, hevsmall] with s hs hsmall
    have h2 := norm_sub_norm_le (D.Y s).inverse (D.Y t).inverse
    nlinarith [hnorm_le hs, h2, hsmall, norm_nonneg (D.Y s - D.Y t),
      norm_nonneg ((D.Y t).inverse), norm_nonneg ((D.Y s).inverse)]
  have hconv : Tendsto (fun s : ℝ => (D.Y s).inverse - (D.Y t).inverse) (𝓝 t) (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero' (g := fun s : ℝ => (2 * ‖(D.Y t).inverse‖ ^ 2) * ‖D.Y s - D.Y t‖)
      (Eventually.of_forall fun s => norm_nonneg _) ?_ ?_
    · filter_upwards [hevint, hbd] with s hs hb
      calc ‖(D.Y s).inverse - (D.Y t).inverse‖
          ≤ ‖(D.Y s).inverse‖ * ‖D.Y s - D.Y t‖ * ‖(D.Y t).inverse‖ := hnorm_le hs
        _ ≤ (2 * ‖(D.Y t).inverse‖) * ‖D.Y s - D.Y t‖ * ‖(D.Y t).inverse‖ := by gcongr
        _ = (2 * ‖(D.Y t).inverse‖ ^ 2) * ‖D.Y s - D.Y t‖ := by ring
    · have h3 : Tendsto (fun s : ℝ => (2 * ‖(D.Y t).inverse‖ ^ 2) * ‖D.Y s - D.Y t‖)
          (𝓝 t) (𝓝 ((2 * ‖(D.Y t).inverse‖ ^ 2) * 0)) := hdtend.const_mul _
      simpa using h3
  have hadd := hconv.add (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (D.Y t).inverse) (𝓝 t) (𝓝 ((D.Y t).inverse)))
  simpa using hadd

/-- The pointwise application of two convergent continuous families. -/
theorem continuous_clm_comp :
    Continuous fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  exact ContinuousAt.clm_comp continuousAt_fst continuousAt_snd

/-- The pointwise application of two convergent continuous families. -/
theorem tendsto_comp {ι : Type*} {l : Filter ι} {A : ι → E →L[ℝ] E} {A₀ : E →L[ℝ] E}
    {B : ι → E →L[ℝ] E} {B₀ : E →L[ℝ] E} (hA : Tendsto A l (𝓝 A₀)) (hB : Tendsto B l (𝓝 B₀)) :
    Tendsto (fun i => (A i).comp (B i)) l (𝓝 (A₀.comp B₀)) :=
  (continuous_clm_comp.tendsto (A₀, B₀)).comp (by
    have h := hA.prodMk hB
    simpa only [← nhds_prod_eq] using h)

/-- The pointwise application of two convergent continuous families. -/
theorem tendsto_apply {ι : Type*} {l : Filter ι} {A : ι → E →L[ℝ] E} {A₀ : E →L[ℝ] E}
    {x : ι → E} {x₀ : E} (hA : Tendsto A l (𝓝 A₀)) (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun i => A i (x i)) l (𝓝 (A₀ x₀)) := by
  have hcont : Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hp : Tendsto (fun i => (A i, x i)) l (𝓝 (A₀, x₀)) := by
    have h := hA.prodMk hx
    simpa only [← nhds_prod_eq] using h
  exact (hcont.tendsto (A₀, x₀)).comp hp

/-- **Derivative of the inverse** on a general window. -/
theorem hasDerivAt_inverse_gen (D : JData cov x₀ q v u w A B) (W : Window D) {t : ℝ}
    (ht : t ∈ Ioo 0 W.T) :
    HasDerivAt (fun s : ℝ => (D.Y s).inverse)
      (-(((D.Y t).inverse).comp (((D.U t - (gammaOp (cov := cov) x₀ u w t).comp (D.Y t))
        ).comp ((D.Y t).inverse)))) t := by
  have ht2 : t ∈ Ioo A B := W.mem ht
  rw [hasDerivAt_iff_tendsto_slope]
  have hevint : ∀ᶠ s : ℝ in 𝓝[≠] t, s ∈ Ioo 0 W.T :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ht)
  have hslope : Tendsto (fun s : ℝ => (s - t)⁻¹ • (D.Y s - D.Y t)) (𝓝[≠] t)
      (𝓝 (D.U t - (gammaOp (cov := cov) x₀ u w t).comp (D.Y t))) :=
    (D.hY t ht2).tendsto_slope
  have htinv : Tendsto (fun s : ℝ => (D.Y s).inverse) (𝓝[≠] t) (𝓝 ((D.Y t).inverse)) :=
    (tendsto_inverse_gen D W ht).mono_left nhdsWithin_le_nhds
  have hcongr : (fun s : ℝ => slope (fun r : ℝ => (D.Y r).inverse) t s) =ᶠ[𝓝[≠] t]
      (fun s : ℝ => -(((D.Y s).inverse).comp (((s - t)⁻¹ • (D.Y s - D.Y t)).comp
        ((D.Y t).inverse)))) := by
    filter_upwards [hevint] with s hs
    rw [slope_def_module, inverse_diff_gen D (W.hYinv s hs) (W.hYinv t ht)]
    rw [smul_neg, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  refine Tendsto.congr' hcongr.symm ?_
  exact (tendsto_comp htinv (tendsto_comp hslope tendsto_const_nhds)).neg

/-! ## The shape operator and the Riccati equation -/

/-- The **shape operator** `Ŝ t = U t ∘ (Y t)⁻¹` of the Jacobi tensor. -/
noncomputable def shapeOp (D : JData cov x₀ q v u w A B) (t : ℝ) : E →L[ℝ] E :=
  (D.U t).comp ((D.Y t).inverse)

lemma shapeOp_apply (D : JData cov x₀ q v u w A B) (t : ℝ) (x : E) :
    D.shapeOp t x = (D.U t) ((D.Y t).inverse x) := by
  simp only [shapeOp, ContinuousLinearMap.comp_apply]

/-- `Ŝ (Y a) = U a`, pointwise form. -/
lemma shapeOp_Y_gen (D : JData cov x₀ q v u w A B) {t : ℝ} (h : (D.Y t).IsInvertible) (x : E) :
    D.shapeOp t (D.Y t x) = D.U t x := by
  rw [shapeOp_apply, inverse_apply_Y_gen D h x]

/-- The derivative of the shape operator, in the form of the **covariant Riccati equation**
`Ŝ' = -Γ̂Ŝ - Rop - Ŝ² + ŜΓ̂`. -/
noncomputable def shapeOpDeriv (D : JData cov x₀ q v u w A B) (t : ℝ) : E →L[ℝ] E :=
  -((gammaOp (cov := cov) x₀ u w t).comp (D.shapeOp t))
    - (curvOp (cov := cov) x₀ u w t)
    - (D.shapeOp t).comp (D.shapeOp t)
    + (D.shapeOp t).comp (gammaOp (cov := cov) x₀ u w t)

/-- **The Riccati equation** on a general window. -/
theorem hasDerivAt_shapeOp_gen (D : JData cov x₀ q v u w A B) (W : Window D) {t : ℝ}
    (ht : t ∈ Ioo 0 W.T) :
    HasDerivAt (fun s : ℝ => D.shapeOp s) (D.shapeOpDeriv t) t := by
  have ht2 : t ∈ Ioo A B := W.mem ht
  have hprod := (D.hU t ht2).clm_comp (hasDerivAt_inverse_gen D W ht)
  have key : (-((gammaOp (cov := cov) x₀ u w t).comp (D.U t))
          - (curvOp (cov := cov) x₀ u w t).comp (D.Y t)).comp ((D.Y t).inverse)
        + (D.U t).comp (-(((D.Y t).inverse).comp (((D.U t
            - (gammaOp (cov := cov) x₀ u w t).comp (D.Y t))).comp ((D.Y t).inverse))))
      = D.shapeOpDeriv t := by
    ext x
    simp only [shapeOpDeriv, shapeOp, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, map_sub, map_neg]
    rw [Y_apply_inverse_gen D (W.hYinv t ht) x]
    abel
  rw [key] at hprod
  simpa only [shapeOp] using hprod

/-- The covariant derivative `∇Ŝ = Ŝ' + Γ̂Ŝ - ŜΓ̂` of the shape operator. -/
noncomputable def nablaShape (D : JData cov x₀ q v u w A B) (t : ℝ) : E →L[ℝ] E :=
  D.shapeOpDeriv t + (gammaOp (cov := cov) x₀ u w t).comp (D.shapeOp t)
    - (D.shapeOp t).comp (gammaOp (cov := cov) x₀ u w t)

/-- **Riccati's equation in covariant form**: `∇Ŝ = -Ŝ² - R`. -/
theorem nablaShape_eq (D : JData cov x₀ q v u w A B) (t : ℝ) :
    D.nablaShape t = -((D.shapeOp t).comp (D.shapeOp t)) - (curvOp (cov := cov) x₀ u w t) := by
  ext x
  simp only [nablaShape, shapeOpDeriv, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply]
  abel

/-- The scalar Riccati quantity `w(t) = ⟨Ŝ(t) e(t), e(t)⟩` of a field `e` along the geodesic. -/
noncomputable def riccatiW (D : JData cov x₀ q v u w A B) (e : ℝ → E) (t : ℝ) : ℝ :=
  chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (D.shapeOp t (e t)) (e t)

lemma riccatiW_apply (D : JData cov x₀ q v u w A B) (e : ℝ → E) (t : ℝ) :
    D.riccatiW e t
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (D.shapeOp t (e t)) (e t) := rfl

/-- **Self-adjointness of the shape operator** on a general window. -/
theorem shapeOp_self_adjoint_gen (D : JData cov x₀ q v u w A B) (W : Window D) {t : ℝ}
    (ht : t ∈ Ioo 0 W.T) (x y : E) :
    chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (D.shapeOp t x) y
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) x (D.shapeOp t y) := by
  have ht2 : t ∈ Ioo A B := W.mem ht
  have hYt := W.hYinv t ht
  have hx := Y_apply_inverse_gen D hYt x
  have hy := Y_apply_inverse_gen D hYt y
  have hw := wronskian_eq_zero_Ioo (cov := cov) D
    (a := (D.Y t).inverse x) (b := (D.Y t).inverse y) ht2
  rw [hx, hy] at hw
  simpa only [shapeOp, ContinuousLinearMap.comp_apply] using hw

/-- **The derivative of the Riccati quantity** on a general window. -/
theorem hasDerivAt_riccatiW_gen (D : JData cov x₀ q v u w A B) (W : Window D) {e : ℝ → E}
    (he : ∀ t ∈ Icc 0 W.T,
      HasDerivAt e (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (e t)) t)
    {t : ℝ} (ht : t ∈ Ioo 0 W.T) :
    HasDerivAt (D.riccatiW e)
      (-(chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (D.shapeOp t (e t)) (D.shapeOp t (e t)))
        - chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            ((curvOp (cov := cov) x₀ u w t) (e t)) (e t)) t := by
  have ht2 : t ∈ Ioo A B := W.mem ht
  have htIcc : t ∈ Icc 0 W.T := ⟨ht.1.le, ht.2.le⟩
  have hutgt : u t ∈ (extChartAt I x₀).target := D.hgeo.2.2.1 t ht2
  have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    (D.hgeo.2.2.2.1 t ht2).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds hutgt)
  have hederiv : HasDerivAt e (deriv e t) t :=
    (he t htIcc).congr_deriv (he t htIcc).deriv.symm
  have hecov : chartCovDeriv cov x₀ u w e t = 0 :=
    chartCovDeriv_eq_zero_of_hasDerivAt (he t htIcc)
  have hV : HasDerivAt (fun s => D.shapeOp s (e s))
      ((D.shapeOpDeriv t) (e t) + (D.shapeOp t) (deriv e t)) t :=
    (hasDerivAt_shapeOp_gen D W ht).clm_apply hederiv
  have hV' : HasDerivAt (fun s => D.shapeOp s (e s))
      (deriv (fun s => D.shapeOp s (e s)) t) t :=
    hV.congr_deriv hV.deriv.symm
  have hmain := hasDerivAt_chartGram_chartCovDeriv (cov := cov) D.hmet x₀
    (D.hgeo.2.2.2.1 t ht2) hutgt hstay hV' hederiv
  have hcovV : chartCovDeriv cov x₀ u w (fun s => D.shapeOp s (e s)) t
      = (D.nablaShape t) (e t) := by
    have hde : deriv e t = -(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (e t) :=
      (he t htIcc).deriv
    rw [chartCovDeriv, hV.deriv, hde]
    simp only [nablaShape, shapeOpDeriv, gammaOp, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, map_neg]
    abel
  have hval : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (chartCovDeriv cov x₀ u w (fun s => D.shapeOp s (e s)) t) (e t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (D.shapeOp t (e t)) (chartCovDeriv cov x₀ u w e t)
      = (-(chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (D.shapeOp t (e t)) (D.shapeOp t (e t)))
        - chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            ((curvOp (cov := cov) x₀ u w t) (e t)) (e t)) := by
    rw [hcovV, hecov, chartGram_zero_snd, add_zero, D.nablaShape_eq]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply]
    rw [sub_eq_add_neg, chartGram_add_fst, chartGram_neg_fst, chartGram_neg_fst,
      shapeOp_self_adjoint_gen D W ht (D.shapeOp t (e t)) (e t)]
    ring
  exact hmain.congr_deriv hval

/-- **The scalar Riccati inequality** on a general window. -/
theorem deriv_riccatiW_add_sq_add_one_le_gen (D : JData cov x₀ q v u w A B) (W : Window D)
    {e : ℝ → E}
    (he : ∀ t ∈ Icc 0 W.T,
      HasDerivAt e (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (e t)) t)
    (he1 : ∀ t ∈ Icc 0 W.T,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (e t) (e t) = 1)
    (he2 : ∀ t ∈ Icc 0 W.T,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (e t) (w t) = 0)
    {t : ℝ} (ht : t ∈ Ioo 0 W.T) :
    deriv (D.riccatiW e) t + (D.riccatiW e t) ^ 2 + 1 ≤ 0 := by
  have ht2 : t ∈ Ioo A B := W.mem ht
  have htIcc : t ∈ Icc 0 W.T := ⟨ht.1.le, ht.2.le⟩
  have hsrc := mem_source_chartCurve (I := I) (D.hgeo.2.2.1 t ht2)
  have hde : deriv (D.riccatiW e) t
      = -(chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (D.shapeOp t (e t)) (D.shapeOp t (e t)))
        - chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            ((curvOp (cov := cov) x₀ u w t) (e t)) (e t) :=
    (hasDerivAt_riccatiW_gen D W he ht).deriv
  have hcs := chartGram_sq_le (I := I) x₀ ((extChartAt I x₀).symm (u t))
    (D.shapeOp t (e t)) (e t)
  rw [he1 t htIcc, mul_one] at hcs
  have hcurv : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (e t) (e t)
      ≤ chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          ((curvOp (cov := cov) x₀ u w t) (e t)) (e t) := by
    rw [curvOp_apply (cov := cov) hsrc]
    exact chartCurv_lower_bound_normal (cov := cov)
      (hcov := ‹ContMDiffCovariantDerivative cov ∞›)
      D.htor D.hmet D.hpinch x₀ hsrc (D.hunit t ht2) (he2 t htIcc)
  rw [hde, riccatiW_apply]
  linarith [hcs, hcurv, he1 t htIcc]



/-- The scaled inverse of `Y`, pointwise form. -/
theorem inverse_smul_Y_gen (D : JData cov x₀ q v u w A B) {t : ℝ} (h : (D.Y t).IsInvertible)
    {c : ℝ} (hc : c ≠ 0) :
    (c • D.Y t).inverse = c⁻¹ • (D.Y t).inverse := by
  have h1 : (c • D.Y t).comp (c⁻¹ • (D.Y t).inverse) = 1 := by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      h.self_comp_inverse, smul_smul, mul_inv_cancel₀ hc, one_smul]
    rfl
  have h2 : (c⁻¹ • (D.Y t).inverse).comp (c • D.Y t) = 1 := by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      h.inverse_comp_self, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rfl
  exact ContinuousLinearMap.inverse_eq h1 h2

/-- `t • Ŝ t = U t ∘ (t⁻¹ • Y t)⁻¹`, pointwise form. -/
theorem smul_shapeOp_gen (D : JData cov x₀ q v u w A B) {t : ℝ} (h : (D.Y t).IsInvertible)
    (ht : t ≠ 0) :
    t • D.shapeOp t = (D.U t).comp ((t⁻¹ • D.Y t).inverse) := by
  rw [shapeOp, inverse_smul_Y_gen D h (inv_ne_zero ht), inv_inv,
    ContinuousLinearMap.comp_smul]

/-- **The initial asymptotics of the shape operator** on a general window. -/
theorem tendsto_smul_shapeOp_gen (D : JData cov x₀ q v u w A B) (W : Window D) :
    Tendsto (fun t : ℝ => t • D.shapeOp t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h0 : (0 : ℝ) ∈ Ioo A B := ⟨D.hA, D.hB⟩
  have hU1 : Tendsto (fun t : ℝ => D.U t) (𝓝[>] (0 : ℝ)) (𝓝 (1 : E →L[ℝ] E)) := by
    have h : Tendsto (fun t : ℝ => D.U t) (𝓝 (0 : ℝ)) (𝓝 (1 : E →L[ℝ] E)) := by
      simpa only [D.hU0] using (D.hU 0 h0).continuousAt.tendsto
    exact h.mono_left nhdsWithin_le_nhds
  have hG : Tendsto (fun t : ℝ => (gammaOp (cov := cov) x₀ u w t).comp (D.Y t))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : E →L[ℝ] E)) := by
    have hg : Tendsto (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) (𝓝[>] (0 : ℝ))
        (𝓝 (gammaOp (cov := cov) x₀ u w 0)) :=
      ((D.continuousOn_gammaOp_Ioo.continuousAt
        (isOpen_Ioo.mem_nhds h0)).tendsto.mono_left nhdsWithin_le_nhds)
    have hy : Tendsto D.Y (𝓝[>] (0 : ℝ)) (𝓝 (D.Y 0)) :=
      ((D.hY 0 h0).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have h := tendsto_comp hg hy
    rw [D.hY0, ContinuousLinearMap.comp_zero] at h
    exact h
  have hB : Tendsto (fun t : ℝ => t⁻¹ • D.Y t) (𝓝[>] (0 : ℝ)) (𝓝 (1 : E →L[ℝ] E)) := by
    refine Commons.Analysis.Calculus.tendsto_inv_smul_of_tendsto_deriv
      (T := W.T) (a := (1 : E →L[ℝ] E)) W.hT ?_ D.hY0 ?_ ?_
    · intro t ht
      have ht2 : t ∈ Ioo A B := ⟨by linarith [D.hA, ht.1], by linarith [W.hTB, ht.2]⟩
      exact (D.hY t ht2).congr_deriv (D.hY t ht2).deriv.symm
    · have h : Tendsto D.Y (𝓝 (0 : ℝ)) (𝓝 (0 : E →L[ℝ] E)) := by
        simpa only [D.hY0] using (D.hY 0 h0).continuousAt.tendsto
      exact h.mono_left nhdsWithin_le_nhds
    · have hde : (fun t : ℝ => deriv D.Y t) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun t : ℝ => D.U t - (gammaOp (cov := cov) x₀ u w t).comp (D.Y t)) := by
        filter_upwards [Ioo_mem_nhdsGT W.hT] with t ht
        have ht2 : t ∈ Ioo A B := ⟨by linarith [D.hA, ht.1], by linarith [W.hTB, ht.2]⟩
        simpa only [gammaOp] using (D.hY t ht2).deriv
      have h2 : Tendsto (fun t : ℝ => D.U t - (gammaOp (cov := cov) x₀ u w t).comp (D.Y t))
          (𝓝[>] (0 : ℝ)) (𝓝 (1 : E →L[ℝ] E)) := by
        have h3 := hU1.sub hG
        simpa using h3
      exact h2.congr' hde.symm
  have hBinv := Commons.Analysis.Normed.Operator.tendsto_inverse_of_tendsto_one hB
  have hcomp : Tendsto (fun t : ℝ => (D.U t).comp ((t⁻¹ • D.Y t).inverse))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : E →L[ℝ] E)) := by
    have h := tendsto_comp hU1 hBinv
    have h11 : (1 : E →L[ℝ] E).comp (1 : E →L[ℝ] E) = 1 := by ext x; simp
    rw [h11] at h
    exact h
  refine hcomp.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT W.hT] with t ht
  exact (smul_shapeOp_gen D (W.hYinv t ht) (ne_of_gt ht.1)).symm

/-- **The asymptotics of the Riccati quantity** on a general window: `t w(t) → 1`. -/
theorem tendsto_riccatiW_mul_gen (D : JData cov x₀ q v u w A B) (W : Window D) {e : ℝ → E}
    (he : ∀ t ∈ Icc 0 W.T,
      HasDerivAt e (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (e t)) t)
    (he1 : ∀ t ∈ Icc 0 W.T,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (e t) (e t) = 1) :
    Tendsto (fun t : ℝ => D.riccatiW e t * t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h0 : (0 : ℝ) ∈ Ioo A B := ⟨D.hA, D.hB⟩
  have h0Icc : (0 : ℝ) ∈ Icc 0 W.T := ⟨le_rfl, W.hT.le⟩
  have hutgt : u 0 ∈ (extChartAt I x₀).target := D.hgeo.2.2.1 0 h0
  have huc : Tendsto (fun t : ℝ => (extChartAt I x₀).symm (u t)) (𝓝[>] (0 : ℝ))
      (𝓝 ((extChartAt I x₀).symm (u 0))) :=
    ((continuousAt_extChartAt_symm'' hutgt).comp (D.hgeo.2.2.2.1 0 h0).continuousAt).tendsto
      |>.mono_left nhdsWithin_le_nhds
  have hec : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 (e 0)) :=
    ((he 0 h0Icc).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hVt : Tendsto (fun t : ℝ => (t • D.shapeOp t) (e t)) (𝓝[>] (0 : ℝ)) (𝓝 (e 0)) := by
    have h := tendsto_apply (tendsto_smul_shapeOp_gen D W) hec
    simpa using h
  have hgram := continuousAt_chartGram_prod3 (I := I) x₀
    (mem_source_chartCurve (I := I) hutgt) (e 0) (e 0)
  have hpair : Tendsto (fun t : ℝ => ((extChartAt I x₀).symm (u t),
      (t • D.shapeOp t) (e t), e t)) (𝓝[>] (0 : ℝ))
      (𝓝 ((extChartAt I x₀).symm (u 0), e 0, e 0)) := by
    have h := huc.prodMk (hVt.prodMk hec)
    simpa only [← nhds_prod_eq] using h
  have hmain : Tendsto (fun t : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
      ((t • D.shapeOp t) (e t)) (e t)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := hgram.tendsto.comp hpair
    rw [he1 0 h0Icc] at h
    exact h
  refine hmain.congr' ?_
  filter_upwards with t
  rw [riccatiW_apply, ContinuousLinearMap.smul_apply, chartGram_smul_fst]
  ring

/-- **The Riccati comparison** on a general window. -/
theorem riccati_parallel_gen (D : JData cov x₀ q v u w A B) (W : Window D) {e : ℝ → E}
    (he : ∀ t ∈ Icc 0 W.T,
      HasDerivAt e (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (e t)) t)
    (he1 : ∀ t ∈ Icc 0 W.T,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (e t) (e t) = 1)
    (he2 : ∀ t ∈ Icc 0 W.T,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (e t) (w t) = 0) :
    ∀ t ∈ Ioo 0 W.T, D.riccatiW e t ≤ Real.cot t := by
  have hw : ∀ t ∈ Ioo 0 W.T, HasDerivAt (D.riccatiW e) (deriv (D.riccatiW e) t) t :=
    fun t ht => (hasDerivAt_riccatiW_gen D W he ht).congr_deriv
      (hasDerivAt_riccatiW_gen D W he ht).deriv.symm
  have hineq : ∀ t ∈ Ioo 0 W.T,
      deriv (D.riccatiW e) t + (D.riccatiW e t) ^ 2 + 1 ≤ 0 :=
    fun t ht => deriv_riccatiW_add_sq_add_one_le_gen D W he he1 he2 ht
  have hasym : Tendsto (fun t : ℝ =>
      (D.riccatiW e t - Real.sqrt 1 * Real.cot (Real.sqrt 1 * t)) * t ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := Commons.Analysis.Calculus.tendsto_cot_asymptotic_of_mul_tendsto_one
      (tendsto_riccatiW_mul_gen D W he he1)
    simpa using h
  have hmain := Commons.Analysis.ODE.riccati_le_cot (w := D.riccatiW e)
    (by norm_num : (0 : ℝ) < 1) W.hT hw hineq hasym
  have hmin : min W.T (Real.pi / Real.sqrt 1) = W.T := by
    rw [Real.sqrt_one, div_one]
    exact min_eq_left (le_of_lt W.lt_pi)
  intro t ht
  have ht' : t ∈ Ioo 0 (min W.T (Real.pi / Real.sqrt 1)) := by
    rw [hmin]; exact ht
  have h := hmain t ht'
  simpa [Real.sqrt_one] using h

/-- **Existence of a parallel unit normal field** with prescribed value at `t₀`. -/
theorem exists_parallel_unit_normal_gen (D : JData cov x₀ q v u w A B) (W : Window D) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo 0 W.T) {u₀ : E}
    (hu₀ : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) u₀ u₀ = 1)
    (hu₀' : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) u₀ (w t₀) = 0) :
    ∃ e : ℝ → E, e t₀ = u₀ ∧
      (∀ t ∈ Icc 0 W.T, HasDerivAt e (-(christoffelLM cov x₀
        ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (e t)) t) ∧
      (∀ t ∈ Icc 0 W.T,
        chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (e t) (e t) = 1) ∧
      (∀ t ∈ Icc 0 W.T,
        chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (e t) (w t) = 0) := by
  have habt : Icc (0 : ℝ) W.T ⊆ Ioo A B := by
    intro t ht
    exact ⟨lt_of_lt_of_le D.hA ht.1, lt_of_le_of_lt ht.2 W.hTB⟩
  have ht₀Icc : t₀ ∈ Icc (0 : ℝ) W.T := ⟨ht₀.1.le, ht₀.2.le⟩
  obtain ⟨e, he₀, he, -⟩ := exists_parallel_field_Ioo (cov := cov) D.htor W.hT habt
    (fun t ht => D.hgeo.2.2.1 t ht) (fun t ht => D.hgeo.2.2.2.1 t ht)
    (fun t ht => D.hgeo.2.2.2.2 t ht) ht₀Icc u₀
  refine ⟨e, he₀, he, ?_, ?_⟩
  · intro t ht
    have h := chartGram_parallel_self_const_Ioo (cov := cov) D.hmet
      (fun t ht => D.hgeo.2.2.1 t ht) (fun t ht => D.hgeo.2.2.2.1 t ht)
      (fun t ht => D.hgeo.2.2.2.2 t ht) W.hT.le habt ht₀Icc he
    rw [h t ht, he₀, hu₀]
  · intro t ht
    have hwpar : ∀ s ∈ Icc (0 : ℝ) W.T, HasDerivAt w (-(christoffelLM cov x₀
        ((extChartAt I x₀).symm (u s))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u s)) (w s))) (w s)) s :=
      fun s hs => Submission.JacobiGen.hasDerivAt_velocity_Ioo (cov := cov)
        (fun t ht => D.hgeo.2.2.2.1 t ht) (fun t ht => D.hgeo.2.2.2.2 t ht)
        (fun t ht => D.hgeo.2.2.1 t ht) s (habt hs)
    have h := chartGram_parallel_const_Ioo (cov := cov) D.hmet
      (fun t ht => D.hgeo.2.2.1 t ht) (fun t ht => D.hgeo.2.2.2.1 t ht)
      (fun t ht => D.hgeo.2.2.2.2 t ht) W.hT.le habt ht₀Icc he hwpar
    rw [h t ht, he₀, hu₀']

/-- **Loewner's bound**: `⟨Ŝ(t₀) u, u⟩ ≤ cot t₀ ⟨u, u⟩` for `u ⊥ γ'(t₀)`. -/
theorem loewner_gen (D : JData cov x₀ q v u w A B) (W : Window D) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo 0 W.T) {u₀ : E}
    (hu₀ : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) u₀ (w t₀) = 0) :
    chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (D.shapeOp t₀ u₀) u₀
      ≤ Real.cot t₀ * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) u₀ u₀ := by
  rcases eq_or_ne u₀ 0 with h0 | h0
  · subst h0
    rw [map_zero, chartGram_zero_snd, mul_zero]
  have ht2 : t₀ ∈ Ioo A B := W.mem ht₀
  have hsrc := mem_source_chartCurve (I := I) (D.hgeo.2.2.1 t₀ ht2)
  have hgnn : 0 ≤ chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) u₀ u₀ := by
    rw [chartGram_apply]
    exact real_inner_self_nonneg
  have hgne : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) u₀ u₀ ≠ 0 := by
    intro h
    exact h0 ((chartGram_self_eq_zero_iff (I := I) hsrc u₀).mp h)
  set c : ℝ := Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) u₀ u₀)
  have hcpos : 0 < c := Real.sqrt_pos.mpr (lt_of_le_of_ne hgnn (Ne.symm hgne))
  have hcsq : c ^ 2 = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) u₀ u₀ :=
    Real.sq_sqrt hgnn
  have hu₁ : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (c⁻¹ • u₀) (c⁻¹ • u₀) = 1 := by
    rw [chartGram_smul_fst, chartGram_smul_snd, ← hcsq]
    field_simp
  have hu₁' : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (c⁻¹ • u₀) (w t₀) = 0 := by
    rw [chartGram_smul_fst, hu₀, mul_zero]
  obtain ⟨e, he₀, he, he1, he2⟩ := exists_parallel_unit_normal_gen D W ht₀ hu₁ hu₁'
  have hw := riccati_parallel_gen D W he he1 he2 t₀ ht₀
  have hev : D.riccatiW e t₀
      = (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (D.shapeOp t₀ u₀) u₀) / c ^ 2 := by
    rw [riccatiW_apply, he₀, map_smul, chartGram_smul_fst, chartGram_smul_snd]
    field_simp
  have hw2 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (D.shapeOp t₀ u₀) u₀
      ≤ Real.cot t₀ * c ^ 2 := by
    rw [hev, div_le_iff₀ (by positivity : (0 : ℝ) < c ^ 2)] at hw
    exact hw
  rw [← hcsq]
  exact hw2




/-- The curvature form is orthogonal to the velocity: `⟨R(X,Y)Y, Y⟩ = 0`. -/
theorem chartCurv_inner_last_gen (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source) (X Y : E) :
    chartGram (I := I) x₀ p (chartCurv cov x₀ p X Y) Y = 0 := by
  have hcov : ContMDiffCovariantDerivative cov ∞ := ‹ContMDiffCovariantDerivative cov ∞›
  rw [chartGram_apply, ← curvVec_frameVector_eq (cov := cov) htor x₀ hp X Y]
  have hskew := inner_curvVec_skew cov hcov hmet p
    (frameVector (I := I) x₀ p X) (frameVector (I := I) x₀ p Y)
    (frameVector (I := I) x₀ p Y) (frameVector (I := I) x₀ p Y)
  have h2 := real_inner_comm (curvVec cov p (frameVector (I := I) x₀ p X)
    (frameVector (I := I) x₀ p Y) (frameVector (I := I) x₀ p Y)) (frameVector (I := I) x₀ p Y)
  linarith [hskew, h2]

/-- **A Jacobi field with `J(0) = 0` and `J'(0) ⊥ γ'(0)` stays perpendicular to the geodesic.** -/
theorem jacobi_normal_gen (D : JData cov x₀ q v u w A B) {a : E}
    (ha : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) a (w 0) = 0) :
    ∀ t ∈ Ioo A B,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (D.Y t a) (w t) = 0 := by
  have hvel : ∀ t ∈ Ioo A B, HasDerivAt w (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (w t)) t :=
    fun t ht => Submission.JacobiGen.hasDerivAt_velocity_Ioo (cov := cov)
      (fun s hs => D.hgeo.2.2.2.1 s hs) (fun s hs => D.hgeo.2.2.2.2 s hs)
      (fun s hs => D.hgeo.2.2.1 s hs) t ht
  -- the derivative of `s ↦ ⟨Y s a, w s⟩` is `s ↦ ⟨U s a, w s⟩`
  have hF : ∀ t ∈ Ioo A B,
      HasDerivAt (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
          (D.Y s a) (w s))
        (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (D.U t a) (w t)) t := by
    intro t ht
    have hutgt : u t ∈ (extChartAt I x₀).target := D.hgeo.2.2.1 t ht
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      (D.hgeo.2.2.2.1 t ht).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds hutgt)
    have h1 : HasDerivAt (fun s => D.Y s a) (deriv (fun s => D.Y s a) t) t := by
      have hh := hasDerivAt_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a)
        (D.hY t ht)
      rw [hh.deriv]; exact hh
    have h2 : HasDerivAt w (deriv w t) t := by
      have hh := hvel t ht
      rw [hh.deriv]; exact hh
    have hmain := hasDerivAt_chartGram_chartCovDeriv (cov := cov) D.hmet x₀
      (D.hgeo.2.2.2.1 t ht) hutgt hstay h1 h2
    have hc1 : chartCovDeriv cov x₀ u w (fun s => D.Y s a) t = D.U t a :=
      chartCovDeriv_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a)
        (D.hY t ht)
    have hc2 : chartCovDeriv cov x₀ u w w t = 0 :=
      chartCovDeriv_eq_zero_of_hasDerivAt (hvel t ht)
    rw [hc1, hc2, chartGram_zero_snd, add_zero] at hmain
    exact hmain
  -- the derivative of `s ↦ ⟨U s a, w s⟩` vanishes
  have hG : ∀ t ∈ Ioo A B,
      HasDerivAt (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
          (D.U s a) (w s)) 0 t := by
    intro t ht
    have hutgt : u t ∈ (extChartAt I x₀).target := D.hgeo.2.2.1 t ht
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      (D.hgeo.2.2.2.1 t ht).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds hutgt)
    have h1 : HasDerivAt (fun s => D.U s a) (deriv (fun s => D.U s a) t) t := by
      have hh := hasDerivAt_jacobiCol_covDeriv_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
        (a := a) (D.hU t ht)
      rw [hh.deriv]; exact hh
    have h2 : HasDerivAt w (deriv w t) t := by
      have hh := hvel t ht
      rw [hh.deriv]; exact hh
    have hmain := hasDerivAt_chartGram_chartCovDeriv (cov := cov) D.hmet x₀
      (D.hgeo.2.2.2.1 t ht) hutgt hstay h1 h2
    have hc1 : chartCovDeriv cov x₀ u w (fun s => D.U s a) t
        = -((curvOp (cov := cov) x₀ u w t) ((D.Y t) a)) :=
      chartCovDeriv_U_const_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (D.hU t ht)
    have hc2 : chartCovDeriv cov x₀ u w w t = 0 :=
      chartCovDeriv_eq_zero_of_hasDerivAt (hvel t ht)
    rw [hc1, hc2, chartGram_zero_snd, add_zero, chartGram_neg_fst] at hmain
    refine hmain.congr_deriv ?_
    rw [curvOp_apply (cov := cov) (mem_source_chartCurve (I := I) hutgt)]
    exact neg_eq_zero.mpr (chartCurv_inner_last_gen (cov := cov) D.htor D.hmet x₀
      (mem_source_chartCurve (I := I) hutgt) ((D.Y t) a) (w t))
  -- `⟨U s a, w s⟩` is constant and vanishes at `0`
  have hGc : ∀ t ∈ Ioo A B,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (D.U t a) (w t) = 0 := by
    intro t ht
    have hsub : ∀ x ∈ Icc (min 0 t) (max 0 t), x ∈ Ioo A B := by
      intro x hx
      exact ⟨lt_of_lt_of_le (lt_min D.hA ht.1) hx.1,
        lt_of_le_of_lt hx.2 (max_lt D.hB ht.2)⟩
    have hconst := Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc min_le_max
      (fun x hx => hG x (hsub x hx))
    have h1 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (D.U t a) (w t)
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u (min 0 t)))
            (D.U (min 0 t) a) (w (min 0 t)) :=
      hconst t ⟨min_le_right _ _, le_max_right _ _⟩
    have h2 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) (D.U 0 a) (w 0)
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u (min 0 t)))
            (D.U (min 0 t) a) (w (min 0 t)) :=
      hconst 0 ⟨min_le_left _ _, le_max_left _ _⟩
    rw [h1, ← h2, D.hU0, ContinuousLinearMap.one_apply, ha]
  intro t ht
  have hsub : ∀ x ∈ Icc (min 0 t) (max 0 t), x ∈ Ioo A B := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_min D.hA ht.1) hx.1,
      lt_of_le_of_lt hx.2 (max_lt D.hB ht.2)⟩
  have hFzero : ∀ x ∈ Icc (min 0 t) (max 0 t),
      HasDerivAt (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (D.Y s a) (w s)) 0 x := by
    intro x hx
    refine (hF x (hsub x hx)).congr_deriv ?_
    exact hGc x (hsub x hx)
  have hconst := Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc min_le_max hFzero
  have h1 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (D.Y t a) (w t)
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u (min 0 t)))
          (D.Y (min 0 t) a) (w (min 0 t)) :=
    hconst t ⟨min_le_right _ _, le_max_right _ _⟩
  have h2 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) (D.Y 0 a) (w 0)
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u (min 0 t)))
          (D.Y (min 0 t) a) (w (min 0 t)) :=
    hconst 0 ⟨min_le_left _ _, le_max_left _ _⟩
  rw [h1, ← h2, D.hY0, ContinuousLinearMap.zero_apply, chartGram_zero_fst]

/-! ## Rauch's comparison theorem, upper bound, on a general interval -/

/-- The squared chart norm of the Jacobi field `s ↦ Y s a`. -/
noncomputable def jacobiNormSq (D : JData cov x₀ q v u w A B) (a : E) (s : ℝ) : ℝ :=
  chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (D.Y s a) (D.Y s a)

lemma jacobiNormSq_def (D : JData cov x₀ q v u w A B) (a : E) :
    D.jacobiNormSq a
      = fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (D.Y s a) (D.Y s a) := rfl

lemma jacobiNormSq_apply (D : JData cov x₀ q v u w A B) (a : E) (s : ℝ) :
    D.jacobiNormSq a s
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (D.Y s a) (D.Y s a) := rfl

lemma jacobiNormSq_nonneg (D : JData cov x₀ q v u w A B) (a : E) (s : ℝ) :
    0 ≤ D.jacobiNormSq a s := by
  rw [jacobiNormSq_apply, chartGram_apply]
  exact real_inner_self_nonneg

/-- The derivative of the squared norm of the Jacobi field, on the whole chart interval. -/
theorem hasDerivAt_jacobiNormSq_gen (D : JData cov x₀ q v u w A B) {a : E} {s : ℝ}
    (hs : s ∈ Ioo A B) :
    HasDerivAt (D.jacobiNormSq a)
      (2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (D.U s a) (D.Y s a)) s := by
  have hutgt : u s ∈ (extChartAt I x₀).target := D.hgeo.2.2.1 s hs
  have hstay : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
    (D.hgeo.2.2.2.1 s hs).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds hutgt)
  have h1 : HasDerivAt (fun r => D.Y r a) (deriv (fun r => D.Y r a) s) s := by
    have hh := hasDerivAt_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a)
      (D.hY s hs)
    rw [hh.deriv]; exact hh
  have hmain := hasDerivAt_chartGram_chartCovDeriv (cov := cov) D.hmet x₀
    (D.hgeo.2.2.2.1 s hs) hutgt hstay h1 h1
  have hc1 : chartCovDeriv cov x₀ u w (fun r => D.Y r a) s = D.U s a :=
    chartCovDeriv_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a)
      (D.hY s hs)
  rw [hc1] at hmain
  rw [jacobiNormSq_def]
  convert hmain using 1
  rw [chartGram_comm]
  ring

/-- **Rauch's comparison theorem, upper bound (Rauch I), on a general window.** -/
theorem rauch_upper_gen (D : JData cov x₀ q v u w A B) (W : Window D) {a : E}
    (ha : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) a (w 0) = 0)
    {t : ℝ} (ht : t ∈ Ioo 0 W.T) :
    chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (D.Y t a) (D.Y t a)
      ≤ Real.sin t ^ 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) a a := by
  have h0mem : (0 : ℝ) ∈ Ioo A B := ⟨D.hA, D.hB⟩
  rcases eq_or_ne a 0 with h0 | h0
  · subst h0
    rw [map_zero, chartGram_zero, chartGram_zero, mul_zero]
  set A' : ℝ := chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) a a with hAdef
  have hAnn : 0 ≤ A' := by
    rw [hAdef, chartGram_apply]
    exact real_inner_self_nonneg
  have hAne : A' ≠ 0 := by
    rw [hAdef]
    intro hcon
    exact h0 ((chartGram_self_eq_zero_iff (I := I)
      (mem_source_chartCurve (I := I) (D.hgeo.2.2.1 0 h0mem)) a).mp hcon)
  have hApos : 0 < A' := lt_of_le_of_ne hAnn (Ne.symm hAne)
  -- the Loewner bound for the specific Jacobi field
  have hstep : ∀ s ∈ Ioo 0 W.T,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (D.U s a) (D.Y s a) * Real.sin s
        ≤ Real.cos s * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
            (D.Y s a) (D.Y s a) := by
    intro s hs
    have hs2 : s ∈ Ioo A B := W.mem hs
    have horth : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (D.Y s a) (w s) = 0 :=
      jacobi_normal_gen D ha s hs2
    have hloew := loewner_gen D W hs horth
    rw [shapeOp_Y_gen D (W.hYinv s hs) a] at hloew
    have hsinpos : 0 < Real.sin s :=
      Real.sin_pos_of_pos_of_lt_pi hs.1 (lt_trans hs.2 W.hTpi)
    have hid : (Real.cot s * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
          (D.Y s a) (D.Y s a)) * Real.sin s
        = Real.cos s * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
            (D.Y s a) (D.Y s a) := by
      rw [mul_assoc, mul_comm (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
          (D.Y s a) (D.Y s a)) (Real.sin s), ← mul_assoc, Real.cot_eq_cos_div_sin,
        div_mul_cancel₀ _ (ne_of_gt hsinpos)]
    have h := mul_le_mul_of_nonneg_right hloew hsinpos.le
    rw [hid] at h
    exact h
  -- differentiability of the two sides
  have hf : ∀ s ∈ Ioo 0 W.T,
      HasDerivAt (D.jacobiNormSq a) (deriv (D.jacobiNormSq a) s) s := by
    intro s hs
    exact (hasDerivAt_jacobiNormSq_gen D (W.mem hs)).congr_deriv
      (hasDerivAt_jacobiNormSq_gen D (W.mem hs)).deriv.symm
  have hgsin : ∀ s ∈ Ioo 0 W.T,
      HasDerivAt (fun r : ℝ => Real.sin r ^ 2 * A') (2 * Real.sin s * Real.cos s * A') s := by
    intro s hs
    have h := ((Real.hasDerivAt_sin s).pow 2).mul_const A'
    refine h.congr_deriv ?_
    norm_num
  have hg : ∀ s ∈ Ioo 0 W.T,
      HasDerivAt (fun r : ℝ => Real.sin r ^ 2 * A')
        (deriv (fun r : ℝ => Real.sin r ^ 2 * A') s) s := by
    intro s hs
    exact (hgsin s hs).congr_deriv (hgsin s hs).deriv.symm
  have hgpos : ∀ s ∈ Ioo 0 W.T, 0 < Real.sin s ^ 2 * A' := by
    intro s hs
    have hsinpos : 0 < Real.sin s :=
      Real.sin_pos_of_pos_of_lt_pi hs.1 (lt_trans hs.2 W.hTpi)
    positivity
  have hineq : ∀ s ∈ Ioo 0 W.T,
      deriv (D.jacobiNormSq a) s * (Real.sin s ^ 2 * A')
        ≤ deriv (fun r : ℝ => Real.sin r ^ 2 * A') s * D.jacobiNormSq a s := by
    intro s hs
    rw [(hasDerivAt_jacobiNormSq_gen D (W.mem hs)).deriv, (hgsin s hs).deriv,
      jacobiNormSq_apply, hAdef]
    have hstep' := hstep s hs
    have hsinpos : 0 < Real.sin s :=
      Real.sin_pos_of_pos_of_lt_pi hs.1 (lt_trans hs.2 W.hTpi)
    have h2 : 0 ≤ 2 * Real.sin s * A' := by positivity
    have hmain := mul_le_mul_of_nonneg_left hstep' h2
    nlinarith [hmain]
  -- the asymptotic ratio
  have hder0 : deriv (fun r : ℝ => D.Y r a) 0 = a := by
    rw [(hasDerivAt_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a)
      (D.hY 0 h0mem)).deriv, D.hU0, D.hY0]
    simp
  have hysq : Tendsto (fun s : ℝ =>
      Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (D.Y s a) (D.Y s a)) / s)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt A')) := by
    have hy : HasDerivAt (fun r : ℝ => D.Y r a) (deriv (fun r : ℝ => D.Y r a) 0) 0 :=
      (hasDerivAt_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a)
        (D.hY 0 h0mem)).congr_deriv
        (hasDerivAt_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a)
          (D.hY 0 h0mem)).deriv.symm
    have hy0 : (fun r : ℝ => D.Y r a) 0 = 0 := by
      simp [D.hY0]
    have h := RauchCompare.tendsto_sqrt_chartGram_div (cov := cov) D.hmet
      (D.hgeo.2.2.2.1 0 h0mem) (D.hgeo.2.2.1 0 h0mem) hy hy0
    rw [hder0] at h
    rwa [← hAdef] at h
  have hsq : Tendsto (fun s : ℝ => D.jacobiNormSq a s / s ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 A') := by
    have h := hysq.pow 2
    rw [Real.sq_sqrt hAnn] at h
    refine Tendsto.congr' ?_ h
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [jacobiNormSq_apply, div_pow, Real.sq_sqrt (by
      rw [chartGram_apply]; exact real_inner_self_nonneg)]
  have hsinc : Tendsto (fun s : ℝ => (Real.sinc s)⁻¹ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h : Tendsto Real.sinc (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h := (Real.continuous_sinc.tendsto (0 : ℝ))
      simpa [Real.sinc_zero] using h.mono_left nhdsWithin_le_nhds
    have h2 := (h.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).pow 2
    simpa using h2
  have hlim : Tendsto (fun s : ℝ => D.jacobiNormSq a s / (Real.sin s ^ 2 * A'))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hev : (fun s : ℝ => D.jacobiNormSq a s / (Real.sin s ^ 2 * A')) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun s : ℝ => (D.jacobiNormSq a s / s ^ 2) * (Real.sinc s)⁻¹ ^ 2 / A') := by
      filter_upwards [Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi)] with s hs
      have hs0 : s ≠ 0 := ne_of_gt hs.1
      have hsin : Real.sin s ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hs.1 hs.2)
      rw [Real.sinc_of_ne_zero hs0, inv_div]
      field_simp
    refine Tendsto.congr' hev.symm ?_
    have h := (hsq.mul hsinc).div_const A'
    simpa [div_self hAne] using h
  have hmain := Commons.Analysis.Calculus.le_of_deriv_mul_le_of_tendsto_div
    (f := D.jacobiNormSq a) (g := fun r : ℝ => Real.sin r ^ 2 * A') W.hT
    hf hg hgpos hineq hlim
  have hfin := hmain t ht
  rw [jacobiNormSq_apply, hAdef] at hfin
  exact hfin

/-- The linear (chordal) corollary of Rauch's upper comparison on a general window. -/
theorem rauch_upper_linear_gen (D : JData cov x₀ q v u w A B) (W : Window D) {a : E}
    (ha : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) a (w 0) = 0)
    {t : ℝ} (ht : t ∈ Ioo 0 W.T) :
    chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (D.Y t a) (D.Y t a)
      ≤ t ^ 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) a a := by
  have h := rauch_upper_gen D W ha ht
  have hA : 0 ≤ chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) a a := by
    rw [chartGram_apply]; exact real_inner_self_nonneg
  have hsin : Real.sin t ≤ t := Real.sin_le ht.1.le
  have hsin0 : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (le_of_lt (lt_trans ht.2 W.hTpi))
  have hsq : Real.sin t ^ 2 ≤ t ^ 2 := by nlinarith [hsin, hsin0, ht.1.le]
  have hmul := mul_le_mul_of_nonneg_right hsq hA
  linarith [h, hmul]



/-! ## The conjugate-radius bound: `Y` is invertible before `π/2`

This is the same argument as `Submission/JacobiTensor.lean`'s `jacobiTensor_injective`, but the
Sturm comparison is replaced by the **global** Rauch theorem `RauchGlobal.eqOn_zero_of_jacobi`,
which is available on an arbitrary interval. -/

/-- **Injectivity of the Jacobi tensor before `π/2`** on a general interval. -/
theorem Y_injective_of_mem_gen (D : JData cov x₀ q v u w A B) {t₁ : ℝ}
    (ht₁pos : 0 < t₁) (ht₁π : t₁ < Real.pi / 2) (ht₁B : t₁ < B) :
    Function.Injective (D.Y t₁) := by
  intro a b hab
  set e : E := a - b with hedef
  set y : ℝ → E := fun s => D.Y s e with hydef
  have hy0 : y 0 = 0 := by
    simp only [hydef, D.hY0, ContinuousLinearMap.zero_apply]
  have hyt : y t₁ = 0 := by
    simp only [hydef, hedef, map_sub, hab, sub_self]
  -- the intrinsic Jacobi field
  set γ : ℝ → M := fun s => (extChartAt I x₀).symm (u s) with hγdef
  set J : (s : ℝ) → TangentSpace I (γ s) :=
    fun s => frameVector (I := I) x₀ (γ s) (y s) with hJdef
  have hJ0 : J 0 = 0 := by
    simp only [hJdef, hy0, frameVector_zero']
  have hJt : J t₁ = 0 := by
    simp only [hJdef, hyt, frameVector_zero']
  -- `J` is a Jacobi field near every time
  have hisJ : ∀ t ∈ Ioo A B, IsJacobiAt cov γ J t := by
    intro t ht
    have hnb : Ioo A B ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    refine ⟨x₀, u, w, y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Filter.eventually_of_mem hnb (fun s hs => D.hgeo.2.2.1 s hs)
    · exact Filter.eventually_of_mem hnb (fun s hs => D.hgeo.2.2.2.1 s hs)
    · exact Filter.Eventually.of_forall (fun s => rfl)
    · exact Filter.Eventually.of_forall (fun s => rfl)
    · exact Filter.eventually_of_mem hnb (fun s hs => D.hunit s hs)
    · filter_upwards [hnb] with s hs
      have hh := hasDerivAt_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
        (a := e) (D.hY s hs)
      exact hh.congr_deriv hh.deriv.symm
    · filter_upwards [hnb] with s hs
      have hh := hasDerivAt_chartCovDeriv_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u)
        (w := w) (Y := D.Y) (U := D.U) (a := e) hs D.hY D.hU
      exact hh.congr_deriv hh.deriv.symm
    · filter_upwards [hnb] with s hs
      exact jacobiEquation_col_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
        (Y := D.Y) (U := D.U) (a := e) hs D.hY D.hU
        (mem_source_chartCurve (I := I) (D.hgeo.2.2.1 s hs))
  have heq := Submission.RauchGlobal.eqOn_zero_of_jacobi
    (cov := cov) (hcov := ‹ContMDiffCovariantDerivative cov ∞›) D.hmet D.hpinch D.htor
    (γ := γ) (J := J) D.hA ht₁B hisJ ht₁pos ht₁π hJ0 hJt
  -- consequently `y` vanishes on `(0,t₁)`
  have hyev : (fun s : ℝ => s⁻¹ • (y s - y 0)) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : E)) := by
    filter_upwards [Ioo_mem_nhdsGT ht₁pos] with s hs
    have hsIcc : s ∈ Icc (0:ℝ) t₁ := Ioo_subset_Icc_self hs
    have hJs : J s = 0 := heq s hsIcc
    have hγsrc : γ s ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (D.hgeo.2.2.1 s ⟨by linarith [hs.1, D.hA],
        by linarith [hs.2, ht₁B]⟩)
    have hys : y s = 0 := by
      have h1 : frameVector (I := I) x₀ (γ s) (y s) = 0 := hJs
      exact (frameVector_eq_zero_iff (I := I) hγsrc (y s)).mp h1
    rw [hys, hy0, sub_zero, smul_zero]
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (y t - y 0)) (𝓝[>] (0 : ℝ)) (𝓝 e) := by
    have h0 : (0 : ℝ) ∈ Ioo A B := ⟨D.hA, D.hB⟩
    have hh : HasDerivAt y e 0 := by
      have h := hasDerivAt_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
        (a := e) (D.hY 0 h0)
      refine h.congr_deriv ?_
      rw [D.hY0, D.hU0, ContinuousLinearMap.one_apply, ContinuousLinearMap.zero_apply,
        map_zero, sub_zero]
    simpa only [zero_add] using hh.tendsto_slope_zero_right
  have hzero : Tendsto (fun t : ℝ => t⁻¹ • (y t - y 0)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : E)) :=
    Filter.Tendsto.congr' hyev.symm tendsto_const_nhds
  have he0 : e = 0 := tendsto_nhds_unique hslope hzero
  have hab0 : a - b = 0 := by rw [← hedef]; exact he0
  exact sub_eq_zero.mp hab0

/-- **The Jacobi tensor is invertible before `π/2`** on a general interval. -/
theorem isInvertible_Y_gen (D : JData cov x₀ q v u w A B) {t : ℝ}
    (htpos : 0 < t) (htπ : t < Real.pi / 2) (htB : t < B) :
    (D.Y t).IsInvertible := by
  have hinj : Function.Injective (D.Y t) := D.Y_injective_of_mem_gen htpos htπ htB
  have hsurj : Function.Surjective (D.Y t) :=
    (LinearMap.injective_iff_surjective (f := (D.Y t).toLinearMap)).mp hinj
  refine ⟨(LinearEquiv.ofBijective (D.Y t).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, ?_⟩
  ext x
  rfl


end JData

end

end Submission.RauchGen
