import Submission.Work.RiemLib.RauchGen
import Submission.Work.RiemLib.FlowJacobi
import Submission.Work.RiemLib.Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Gauss's lemma for Jacobi fields along a chart geodesic

This file proves the **Gauss identity** for the columns of a Jacobi tensor along a chart geodesic,
in the form in which it is used for the model bound of the exponential map:

`⟨(Y t) a, w t⟩ = t · ⟨a, w 0⟩`

where `(u, w)` is a chart geodesic, `(Y, U)` solves the Jacobi system (`Y 0 = 0`, `U 0 = 1`) and
`a` is an arbitrary initial variation.  The content is the classical Gauss lemma: the variation
field of a family of geodesics through a common point stays orthogonal to the geodesic exactly when
its initial derivative does (`t = 0` gives `jacobi_normal_gen`), and the *first order* in `t` is
captured by the identity above.

The statement is deliberately *unbundled*: it takes the geodesic-equation data and the Jacobi-system
data as hypotheses, so that it applies to the chart-flow geodesics of `Submission.GExpFlow` (whose
chart speed is not normalised to `1`, so that the bundled `JData` structure does not apply).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.Curvature
open Submission.JacobiTensor
open Submission.Rauch
open Submission.RauchGen
open Submission.FlowJacobi
open Submission.JacobiVec
open Submission.RauchGen.JData
open Submission.Gauss
open Submission.JacobiGen
open Submission.Jacobi
open Submission.Rauch

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.JacobiGauss

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Gauss's lemma for a Jacobi tensor, first-order form.**  Along a chart geodesic `(u,w)` with a
solution `(Y,U)` of the Jacobi system (`Y 0 = 0`, `U 0 = 1`), the pairing of the Jacobi field
`s ↦ (Y s) a` with the velocity is affine in `s` with slope `⟨a, w 0⟩` and value `0` at `0`:
`⟨(Y t) a, w t⟩ = t · ⟨a, w 0⟩`, all inner products being the chart metric at the corresponding
points. -/
theorem jacobi_gauss {x₀ q : M} {v a : E} {A B : ℝ} {u w : ℝ → E} {Y U : ℝ → E →L[ℝ] E}
    (hA : A < 0) (hB : 0 < B) (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hgeo : HasChartGeodesicOn cov x₀ q v u w A B)
    (hY : ∀ t ∈ Ioo A B, HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Ioo A B,
      HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1) {t : ℝ} (ht : t ∈ Ioo A B) :
    chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) ((Y t) a) (w t)
      = t * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) a (w 0) := by
  have hvel : ∀ s ∈ Ioo A B, HasDerivAt w
      (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u s))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u s)) (w s))) (w s)) s :=
    fun s hs => Submission.JacobiGen.hasDerivAt_velocity_Ioo (cov := cov)
      (fun r hr => hgeo.2.2.2.1 r hr) (fun r hr => hgeo.2.2.2.2 r hr)
      (fun r hr => hgeo.2.2.1 r hr) s hs
  -- the derivative of `s ↦ ⟨Y s a, w s⟩` is `s ↦ ⟨U s a, w s⟩`
  have hF : ∀ s ∈ Ioo A B,
      HasDerivAt (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          ((Y r) a) (w r))
        (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((U s) a) (w s)) s := by
    intro s hs
    have hutgt : u s ∈ (extChartAt I x₀).target := hgeo.2.2.1 s hs
    have hstay : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
      (hgeo.2.2.2.1 s hs).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds hutgt)
    have h1 : HasDerivAt (fun r => (Y r) a) (deriv (fun r => (Y r) a) s) s := by
      have hh := hasDerivAt_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a)
        (hY s hs)
      rw [hh.deriv]; exact hh
    have h2 : HasDerivAt w (deriv w s) s := by
      have hh := hvel s hs
      rw [hh.deriv]; exact hh
    have hmain := hasDerivAt_chartGram_chartCovDeriv (cov := cov) hmet x₀
      (hgeo.2.2.2.1 s hs) hutgt hstay h1 h2
    have hc1 : chartCovDeriv cov x₀ u w (fun r => (Y r) a) s = (U s) a :=
      chartCovDeriv_jacobiCol_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a) (hY s hs)
    have hc2 : chartCovDeriv cov x₀ u w w s = 0 :=
      chartCovDeriv_eq_zero_of_hasDerivAt (hvel s hs)
    rw [hc1, hc2, chartGram_zero_snd, add_zero] at hmain
    exact hmain
  -- the derivative of `s ↦ ⟨U s a, w s⟩` vanishes
  have hG : ∀ s ∈ Ioo A B,
      HasDerivAt (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          ((U r) a) (w r)) 0 s := by
    intro s hs
    have hutgt : u s ∈ (extChartAt I x₀).target := hgeo.2.2.1 s hs
    have hstay : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
      (hgeo.2.2.2.1 s hs).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds hutgt)
    have h1 : HasDerivAt (fun r => (U r) a) (deriv (fun r => (U r) a) s) s := by
      have hh := hasDerivAt_jacobiCol_covDeriv_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w)
        (a := a) (hU s hs)
      rw [hh.deriv]; exact hh
    have h2 : HasDerivAt w (deriv w s) s := by
      have hh := hvel s hs
      rw [hh.deriv]; exact hh
    have hmain := hasDerivAt_chartGram_chartCovDeriv (cov := cov) hmet x₀
      (hgeo.2.2.2.1 s hs) hutgt hstay h1 h2
    have hc1 : chartCovDeriv cov x₀ u w (fun r => (U r) a) s
        = -((curvOp (cov := cov) x₀ u w s) ((Y s) a)) :=
      chartCovDeriv_U_const_Ioo (cov := cov) (x₀ := x₀) (u := u) (w := w) (hU s hs)
    have hc2 : chartCovDeriv cov x₀ u w w s = 0 :=
      chartCovDeriv_eq_zero_of_hasDerivAt (hvel s hs)
    rw [hc1, hc2, chartGram_zero_snd, add_zero, chartGram_neg_fst] at hmain
    refine hmain.congr_deriv ?_
    rw [curvOp_apply (cov := cov) (mem_source_chartCurve (I := I) hutgt)]
    exact neg_eq_zero.mpr (chartCurv_inner_last_gen (cov := cov) htor hmet x₀
      (mem_source_chartCurve (I := I) hutgt) ((Y s) a) (w s))
  -- `⟨U s a, w s⟩` is constant
  set C : ℝ := chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) a (w 0) with hC
  have hconstI : ∀ x ∈ Icc (min 0 t) (max 0 t),
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u x)) ((U x) a) (w x)
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u (min 0 t)))
            ((U (min 0 t)) a) (w (min 0 t)) :=
    Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc min_le_max
      (fun y hy => hG y ⟨lt_of_lt_of_le (lt_min hA ht.1) hy.1,
        lt_of_le_of_lt hy.2 (max_lt hB ht.2)⟩)
  have hconst : ∀ x ∈ Icc (min 0 t) (max 0 t),
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u x)) ((U x) a) (w x) = C := by
    intro x hx
    calc chartGram (I := I) x₀ ((extChartAt I x₀).symm (u x)) ((U x) a) (w x)
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u (min 0 t)))
            ((U (min 0 t)) a) (w (min 0 t)) := hconstI x hx
      _ = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) ((U 0) a) (w 0) :=
          (hconstI 0 ⟨min_le_left _ _, le_max_left _ _⟩).symm
      _ = C := by rw [hU0, ContinuousLinearMap.one_apply]
  -- integrate
  set G : ℝ → ℝ := fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
    ((Y r) a) (w r) - r * C with hGdef
  have hprim : ∀ x ∈ Icc (min 0 t) (max 0 t), HasDerivAt G 0 x := by
    intro x hx
    have hsub : x ∈ Ioo A B :=
      ⟨lt_of_lt_of_le (lt_min hA ht.1) hx.1, lt_of_le_of_lt hx.2 (max_lt hB ht.2)⟩
    have hd : HasDerivAt (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
        ((Y r) a) (w r)) C x := (hF x hsub).congr_deriv (hconst x hx)
    have hlin : HasDerivAt (fun r : ℝ => r * C) C x := by
      simpa using (hasDerivAt_id x).mul_const C
    have hsub2 := hd.sub hlin
    have hfun : (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
        ((Y r) a) (w r)) - (fun r : ℝ => r * C) = G := by
      funext r
      simp only [hGdef, Pi.sub_apply]
    rw [hfun] at hsub2
    simpa using hsub2
  have hG0 : G 0 = 0 := by
    simp only [hGdef, hY0, ContinuousLinearMap.zero_apply, chartGram_zero_fst, zero_mul,
      sub_zero]
  have hGt : G t = 0 := by
    have heq := Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc min_le_max hprim
    rw [heq t ⟨min_le_right _ _, le_max_right _ _⟩,
      ← heq 0 ⟨min_le_left _ _, le_max_left _ _⟩, hG0]
  have hval : G t = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) ((Y t) a) (w t)
      - t * C := rfl
  rw [hval] at hGt
  have hgoal : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) ((Y t) a) (w t)
      = t * C := by linarith
  rw [hC] at hgoal
  exact hgoal

/-- The coordinate curvature term vanishes when its two arguments coincide (skew-symmetry of the
first two slots of the curvature). -/
lemma chartCurv_self (x₀ : M) (p : M) (X : E) : chartCurv cov x₀ p X X = 0 := by
  rw [chartCurv]
  abel

/-- **The radial Jacobi field is `t` times the velocity.**  Along a chart geodesic `(u,w)`, the
column `s ↦ (Y s) (w 0)` of the Jacobi tensor (the variation field of the family of geodesics whose
initial *velocity* is varied) equals `s • w s`: the classical statement that the Jacobi field with
`J(0) = 0` and `J'(0) = γ'(0)` is `t γ'(t)`. -/
theorem jacobi_velocity {x₀ q : M} {v : E} {A B : ℝ} {u w : ℝ → E} {Y U : ℝ → E →L[ℝ] E}
    (hA : A < 0) (hB : 0 < B) (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hgeo : HasChartGeodesicOn cov x₀ q v u w A B)
    (hY : ∀ t ∈ Ioo A B, HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Ioo A B,
      HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1) {t : ℝ} (ht : t ∈ Ioo A B) :
    (Y t) (w 0) = t • w t := by
  have hvel : ∀ s ∈ Ioo A B, HasDerivAt w
      (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u s))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u s)) (w s))) (w s)) s :=
    fun s hs => Submission.JacobiGen.hasDerivAt_velocity_Ioo (cov := cov)
      (fun r hr => hgeo.2.2.2.1 r hr) (fun r hr => hgeo.2.2.2.2 r hr)
      (fun r hr => hgeo.2.2.1 r hr) s hs
  have hsub : Icc (min 0 t) (max 0 t) ⊆ Ioo A B := fun s hs =>
    ⟨lt_of_lt_of_le (lt_min hA ht.1) hs.1, lt_of_le_of_lt hs.2 (max_lt hB ht.2)⟩
  have hmem : (0 : ℝ) ∈ Icc (min 0 t) (max 0 t) := ⟨min_le_left _ _, le_max_left _ _⟩
  have hmemt : t ∈ Icc (min 0 t) (max 0 t) := ⟨min_le_right _ _, le_max_right _ _⟩
  -- continuity and boundedness of the Jacobi system on the interval
  have hGon : ContinuousOn (fun s => gammaOp (cov := cov) x₀ u w s)
      (Icc (min 0 t) (max 0 t)) :=
    (Submission.JacobiGen.continuousOn_christoffelLM_along_Ioo (cov := cov) htor
      (fun s hs => hgeo.2.2.1 s hs) (fun s hs => hgeo.2.2.2.1 s hs)
      (fun s hs => hgeo.2.2.2.2 s hs)).mono hsub
  have hwon : ContinuousOn w (Icc (min 0 t) (max 0 t)) :=
    HasDerivAt.continuousOn (fun s hs => hgeo.2.2.2.2 s (hsub hs))
  have hRon : ContinuousOn (fun s => curvOp (cov := cov) x₀ u w s)
      (Icc (min 0 t) (max 0 t)) :=
    Submission.JacobiTensor.continuousOn_curvOp (cov := cov)
      (HasDerivAt.continuousOn (fun s hs => hgeo.2.2.2.1 s (hsub hs))) hwon
      (fun s hs => hgeo.2.2.1 s (hsub hs))
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn hGon
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn hRon
  have hbound : ∀ s ∈ Icc (min 0 t) (max 0 t),
      ‖jacobiSysVec (cov := cov) x₀ u w s‖ ≤ max 0 (1 + 2 * C1 + C2) := by
    intro s hs
    have h6 : ‖jacobiSysVec (cov := cov) x₀ u w s‖
        ≤ 1 + 2 * ‖gammaOp (cov := cov) x₀ u w s‖ + ‖curvOp (cov := cov) x₀ u w s‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
      obtain ⟨y, z⟩ := p
      exact norm_jacobiSysVec_le (cov := cov) x₀ u w s y z
    have h4 : ‖gammaOp (cov := cov) x₀ u w s‖ ≤ C1 := hC1 s hs
    have h5 : ‖curvOp (cov := cov) x₀ u w s‖ ≤ C2 := hC2 s hs
    refine le_trans h6 (le_trans (by linarith) (le_max_right _ _))
  -- the column solution
  have hpairY : ∀ s ∈ Icc (min 0 t) (max 0 t),
      HasDerivAt (fun r => ((Y r) (w 0), (U r) (w 0)))
        (jacobiSysVec (cov := cov) x₀ u w s ((Y s) (w 0), (U s) (w 0))) s := by
    intro s hs
    have h1 : HasDerivAt (fun r => (Y r) (w 0))
        ((U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) (w 0) + (Y s) 0) s :=
      (hY s (hsub hs)).clm_apply (hasDerivAt_const (x := s) (w 0))
    have h1' : HasDerivAt (fun r => (Y r) (w 0))
        ((U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) (w 0)) s := by simpa using h1
    have h2 : HasDerivAt (fun r => (U r) (w 0))
        ((-((gammaOp (cov := cov) x₀ u w s).comp (U s))
          - (curvOp (cov := cov) x₀ u w s).comp (Y s)) (w 0) + (U s) 0) s :=
      (hU s (hsub hs)).clm_apply (hasDerivAt_const (x := s) (w 0))
    have h2' : HasDerivAt (fun r => (U r) (w 0))
        ((-((gammaOp (cov := cov) x₀ u w s).comp (U s))
          - (curvOp (cov := cov) x₀ u w s).comp (Y s)) (w 0)) s := by simpa using h2
    have hbase := h1'.prodMk h2'
    rw [jacobiSysVec_apply]
    refine hbase.congr_deriv ?_
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply]
  -- the radial solution
  have hpairR : ∀ s ∈ Icc (min 0 t) (max 0 t),
      HasDerivAt (fun r => (r • w r, w r))
        (jacobiSysVec (cov := cov) x₀ u w s (s • w s, w s)) s := by
    intro s hs
    have hs' := hsub hs
    have hsrc : (extChartAt I x₀).symm (u s) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (hgeo.2.2.1 s hs')
    have hw : HasDerivAt w (- gammaOp (cov := cov) x₀ u w s (w s)) s := hvel s hs'
    have h1 : HasDerivAt (fun r : ℝ => r • w r)
        (w s - gammaOp (cov := cov) x₀ u w s (s • w s)) s := by
      have h := (hasDerivAt_id s).smul hw
      have hev : (fun r : ℝ => r • w r) =ᶠ[𝓝 s] ((id : ℝ → ℝ) • w) := by
        filter_upwards with r
        rfl
      have hA : HasDerivAt (fun r : ℝ => r • w r)
          (s • (- gammaOp (cov := cov) x₀ u w s (w s)) + (1 : ℝ) • w s) s :=
        h.congr_of_eventuallyEq hev
      refine hA.congr_deriv ?_
      rw [smul_neg, one_smul, map_smul]
      abel
    have h2 : HasDerivAt (fun r : ℝ => w r)
        (- gammaOp (cov := cov) x₀ u w s (w s)
          - curvOp (cov := cov) x₀ u w s (s • w s)) s := by
      refine hw.congr_deriv ?_
      rw [curvOp_apply (cov := cov) (x₀ := x₀) (u := u) (w := w) (t := s) hsrc,
        chartCurv_smul_fst (cov := cov) x₀ ((extChartAt I x₀).symm (u s)) hsrc s (w s) (w s),
        chartCurv_self, smul_zero, sub_zero]
    have hbase := h1.prodMk h2
    rw [jacobiSysVec_apply]
    exact hbase
  -- uniqueness of the linear ODE
  have hinit : ((0 : ℝ) • w 0, w 0) = ((Y 0) (w 0), (U 0) (w 0)) := by
    rw [zero_smul, hY0, hU0]
    simp
  have huniq := Commons.Analysis.ODE.eqOn_of_hasDerivAt_linearODE
    (A := jacobiSysVec (cov := cov) x₀ u w)
    (M := ⟨max 0 (1 + 2 * C1 + C2), le_max_left _ _⟩) hbound hmem hpairR hpairY hinit
  have hfin := Prod.ext_iff.mp (huniq hmemt)
  exact hfin.1.symm

/-- **Gauss's lemma for the exponential map of a chart.**  In the setting of the chart-flow
exponential map `chartFlowExp D q` (i.e. `F (w) = φ⁻¹((D.α (φ q, c • w) c⁻¹).1)`), the pairing of
the differential with the radial direction is the metric at the base point `q`:

`⟨(d F)_u u, (d F)_u y⟩_p = ⟨u, y⟩_q`  (`p = F u`),

all inner products being the chart metric of the chart at `x₀`.  The hypotheses are the ones supplied
by the variation family of the chart flow (see `Submission.ChartFlowModel`); the two ingredients are
`jacobi_gauss` (the off-radial pairing) and `jacobi_velocity` (the radial field is the velocity). -/
theorem chartFlow_gauss {x₀ q : M} {u y : E} {δ : ℝ} {Φ : ℝ × ℝ → E × E} {Y U : ℝ → E →L[ℝ] E}
    (hδ : 0 < δ) (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hqs : q ∈ (extChartAt I x₀).source)
    (hΦ0 : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).1 = (extChartAt I x₀) q)
    (hΦv : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).2 = u + t • y)
    (hgeo : HasChartGeodesicOn cov x₀ q (frameVector (I := I) x₀ q u) (gc Φ) (gv Φ)
      (-(3 / 2)) (3 / 2))
    (hY : ∀ t ∈ Ioo (-(3 / 2) : ℝ) (3 / 2),
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) t)
    (hU : ∀ t ∈ Ioo (-(3 / 2) : ℝ) (3 / 2),
      HasDerivAt U (-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U t))
        - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1) :
    chartGram (I := I) x₀ ((extChartAt I x₀).symm ((gc Φ) 1)) ((Y 1) u) ((Y 1) y)
      = chartGram (I := I) x₀ q u y := by
  have h0δ : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have h1 : (1 : ℝ) ∈ Ioo (-(3 / 2) : ℝ) (3 / 2) := ⟨by norm_num, by norm_num⟩
  -- the value of the family at `t = 0`: the base geodesic
  have hgc0 : (gc Φ) 0 = (extChartAt I x₀) q := by
    show (Φ (0, 0)).1 = (extChartAt I x₀) q
    exact hΦ0 0 h0δ
  have hgv0 : (gv Φ) 0 = u := by
    show (Φ (0, 0)).2 = u
    rw [hΦv 0 h0δ, zero_smul, add_zero]
  -- the radial direction: the column `Y · u` is the velocity
  have hrad : (Y 1) u = (gv Φ) 1 := by
    have hv := jacobi_velocity (cov := cov) (v := frameVector (I := I) x₀ q u)
      (hA := by norm_num) (hB := by norm_num) htor hmet hgeo hY hU hY0 hU0 (t := 1) h1
    rw [hgv0, one_smul] at hv
    exact hv
  -- Gauss's identity for an orthogonal direction
  have hg := jacobi_gauss (cov := cov) (x₀ := x₀) (q := q)
    (v := frameVector (I := I) x₀ q u) (a := y)
    (hA := by norm_num) (hB := by norm_num) htor hmet hgeo hY hU hY0 hU0 (t := 1) h1
  have hbase : (extChartAt I x₀).symm ((gc Φ) 0) = q := by
    rw [hgc0]
    exact (extChartAt I x₀).left_inv hqs
  rw [hbase, hgv0, one_mul] at hg
  rw [← hrad] at hg
  calc chartGram (I := I) x₀ ((extChartAt I x₀).symm ((gc Φ) 1)) ((Y 1) u) ((Y 1) y)
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm ((gc Φ) 1)) ((Y 1) y) ((Y 1) u) :=
        chartGram_comm (I := I) _ _ _ _
    _ = chartGram (I := I) x₀ q y u := hg
    _ = chartGram (I := I) x₀ q u y := chartGram_comm (I := I) _ _ _ _

end

end Submission.JacobiGauss
