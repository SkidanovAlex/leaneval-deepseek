import Submission.Work.RiemLib.ChartGeoAt
import Submission.Work.RiemLib.RauchChart
import Submission.Work.RiemLib.ChartBounds
import Submission.Work.RiemLib.GlobalExp
import Submission.Work.RiemLib.GlobalBM
import Submission.Work.RiemLib.Commons.Analysis.ODE.uniform_flow_joint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The uniform chart flow and the uniform Rauch bound for the global exponential map

`Submission.GlobalExp.GExp hmet q v` is the point at Riemannian distance `‖v‖` from `q` in the
direction `v`.  It is the correct (chart-invariant) exponential map: `Submission.Geodesic.expMap`
depends on the chosen atlas chart at `q`, whose size may be arbitrarily small, so no *uniform*
smoothness statement can be phrased with it (see `Submission/Roadmap.lean` §38).

For the uniform local comparison theorem one needs a uniform bound on the differential of `GExp q`
in a fibre-norm ball whose radius does not depend on `q`.  This file builds it from the flow of the
geodesic spray of a *fixed* chart `z₀`: for points `q` of a compact piece `Z` of the chart at `z₀`,
the geodesic rays of `GExp q` are the flow lines of that spray, so their regularity is uniform.

## Main result

* `exists_uniform_GExp_rauch_bound_of_data` — Rauch's upper bound for `(d GExp_q)_v` on vectors
  `x ⊥ v`, uniformly over `q ∈ Z`.
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
open Submission.Rauch
open Submission.JacobiTensor
open Submission.RauchGen
open Submission.Gauss
open Submission.GlobalExp
open Submission.GeodesicGlobal
open Submission.ChartGeoAt
open Submission.FlowJacobi
open Submission.RauchChart

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GExpFlow

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## The flow data of a fixed chart -/

/-- The geodesic spray of the chart at `z₀`, written as a first-order field on the model space. -/
noncomputable def chartSpray (z₀ : M) (q : E × E) : E × E :=
  (q.2, chartGeodesicVectorField cov z₀ q)

lemma chartSpray_apply (z₀ : M) (q : E × E) :
    chartSpray (cov := cov) z₀ q = (q.2, chartGeodesicVectorField cov z₀ q) := rfl

lemma contDiffOn_chartSpray (z₀ : M) :
    ContDiffOn ℝ ∞ (chartSpray (cov := cov) z₀)
      ((extChartAt I z₀).target ×ˢ (univ : Set E)) :=
  ContDiffOn.prodMk contDiffOn_snd (contDiffOn_chartSpray' (cov := cov) z₀)

/-- The compact set of initial data for the chart at `z₀` attached to a set `Z` of base points:
the chart positions of `Z` and unit coordinate velocities. -/
def chartData (z₀ : M) (Z : Set M) : Set (E × E) :=
  ((extChartAt I z₀) '' Z) ×ˢ closedBall (0 : E) 1

/-- **The uniform flow data of a fixed chart.**  A compact set `Z` of points of the chart at `z₀`
carries a uniform flow of the chart geodesic spray: an open set `O` of initial data containing the
chart positions of `Z` with unit velocities, a time `ρ > 0`, and a family `α` which solves the
chart geodesic equation on `O` for `|t| ≤ ρ`, with *joint* smooth dependence on the initial data
and time and with uniqueness of solutions. -/
structure ChartFlowData (z₀ : M) (Z : Set M) : Type _ where
  ρ : ℝ
  hρ : 0 < ρ
  O : Set (E × E)
  hO : IsOpen O
  hKO : chartData (I := I) z₀ Z ⊆ O
  hOW : O ⊆ (extChartAt I z₀).target ×ˢ (univ : Set E)
  α : E × E → ℝ → E × E
  h0 : ∀ p ∈ O, α p 0 = p
  hode : ∀ p ∈ O, ∀ t : ℝ, |t| ≤ ρ →
    HasDerivAt (α p) (chartSpray (cov := cov) z₀ (α p t)) t
  htgt : ∀ p ∈ O, ∀ t : ℝ, |t| ≤ ρ → (α p t).1 ∈ (extChartAt I z₀).target
  hjoint : ∀ p ∈ chartData (I := I) z₀ Z, ∀ t : ℝ, |t| < ρ →
    ContDiffAt ℝ ∞ (fun q : (E × E) × ℝ => α q.1 q.2) (p, t)
  huniq : ∀ p ∈ O, ∀ β : ℝ → E × E,
    (∀ t : ℝ, |t| ≤ ρ → HasDerivAt β (chartSpray (cov := cov) z₀ (β t)) t) →
    β 0 = p → ∀ t : ℝ, |t| ≤ ρ → β t = α p t

/-! ## Conversion between coordinate vectors and tangent vectors -/

section Conversions

/-- The frame vector of the coordinates of a tangent vector is the vector itself. -/
lemma frameVector_clm {z₀ q : M} (hqs : q ∈ (extChartAt I z₀).source) (v : TangentSpace I q) :
    frameVector (I := I) z₀ q
      ((trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q v) = v := by
  rw [frameVector]
  exact Trivialization.symmL_continuousLinearMapAt (R := ℝ)
    (trivializationAt E (TangentSpace I) z₀) (by simpa using hqs) v

/-- The coordinates of the frame vector with coordinates `w` are `w`. -/
lemma clm_frameVector {z₀ q : M} (hqs : q ∈ (extChartAt I z₀).source) (w : E) :
    (trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q
      (frameVector (I := I) z₀ q w) = w := by
  rw [frameVector]
  exact Trivialization.continuousLinearMapAt_symmL (trivializationAt E (TangentSpace I) z₀)
    (R := ℝ) (by simpa using hqs) w

/-- The chart metric at `q` of the coordinates of two tangent vectors is their inner product. -/
lemma chartGram_clm {z₀ q : M} (hqs : q ∈ (extChartAt I z₀).source) (v w : TangentSpace I q) :
    chartGram (I := I) z₀ q
      ((trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q v)
      ((trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q w)
      = inner ℝ v w :=
  GlobalBM.chartGram_continuousLinearMapAt (I := I) z₀ q (by simpa using hqs) v w

/-- The fibre norm of a frame vector. -/
lemma norm_frameVector {z₀ q : M} (w : E) :
    ‖frameVector (I := I) z₀ q w‖ = Real.sqrt (chartGram (I := I) z₀ q w w) := by
  rw [← Real.sqrt_sq (norm_nonneg (frameVector (I := I) z₀ q w))]
  congr 1
  rw [chartGram_apply, real_inner_self_eq_norm_sq]

/-- The coordinate expression of the norm of a tangent vector. -/
lemma sqrt_chartGram_clm {z₀ q : M} (hqs : q ∈ (extChartAt I z₀).source)
    (v : TangentSpace I q) :
    Real.sqrt (chartGram (I := I) z₀ q
      ((trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q v)
      ((trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q v)) = ‖v‖ := by
  rw [chartGram_clm (I := I) hqs v v, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

end Conversions
/-! ## The identification of `GExp` with the chart flow -/

variable {z₀ : M} {Z : Set M}

/-- The scaling factor relating the flow time of the chart spray to the arclength: the flow of the
chart spray with velocity `c • u` reaches arclength `‖u‖` at flow time `c⁻¹`. -/
noncomputable def flowScale (D : ChartFlowData (cov := cov) (I := I) z₀ Z) : ℝ := 2 / D.ρ

lemma flowScale_pos (D : ChartFlowData (cov := cov) (I := I) z₀ Z) : 0 < flowScale D := by
  rw [flowScale]; exact div_pos two_pos D.hρ

lemma flowScale_ne_zero (D : ChartFlowData (cov := cov) (I := I) z₀ Z) : flowScale D ≠ 0 :=
  ne_of_gt (flowScale_pos D)

lemma inv_flowScale (D : ChartFlowData (cov := cov) (I := I) z₀ Z) :
    (flowScale D)⁻¹ = D.ρ / 2 := by
  rw [flowScale, inv_div]

lemma rho_div_inv_flowScale (D : ChartFlowData (cov := cov) (I := I) z₀ Z) :
    D.ρ / (flowScale D)⁻¹ = 2 := by
  rw [inv_flowScale, div_div_eq_mul_div, mul_comm]
  exact mul_div_cancel_right₀ 2 (ne_of_gt D.hρ)

lemma flowScale_mul_inv (D : ChartFlowData (cov := cov) (I := I) z₀ Z) :
    flowScale D * (flowScale D)⁻¹ = 1 := mul_inv_cancel₀ (flowScale_ne_zero D)

section Ident

variable [Nontrivial E] [CompactSpace M]

/-- **The chart-flow description of `GExp`.**  Let `D` be the flow data of the chart at `z₀` for a
compact piece `Z`, let `q ∈ Z` and let `v ∈ T_qM` be a non-zero tangent vector whose phase
`(φ q, c • coord v)` (with `c = flowScale D`) belongs to the domain `O` of the flow.  Then `GExp q`
agrees, on a ball around `v`, with the time-`c⁻¹` value of the chart flow read through `φ`. -/
theorem GExp_eq_chartFlow (hmet : IsMetricCompatible cov)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {q : M} (hqs : q ∈ (extChartAt I z₀).source) :
    ∀ u : E, ((extChartAt I z₀) q, (flowScale D) • u) ∈ D.O → u ≠ 0 →
      GExp (cov := cov) hmet q (frameVector (I := I) z₀ q u)
        = (extChartAt I z₀).symm
            ((D.α ((extChartAt I z₀) q, (flowScale D) • u) (flowScale D)⁻¹).1) := by
  classical
  intro u hph hu
  set c : ℝ := flowScale D with hcdef
  have hcpos : 0 < c := flowScale_pos D
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcinv : c⁻¹ = D.ρ / 2 := inv_flowScale D
  have hρc : D.ρ / c⁻¹ = 2 := rho_div_inv_flowScale D
  set w : TangentSpace I q := frameVector (I := I) z₀ q u with hwdef
  have hwO : ((extChartAt I z₀) q, c • u) ∈ D.O := hph
  have hwv : 0 < ‖w‖ := by
    rw [hwdef]
    exact norm_pos_iff.mpr (fun h =>
      hu ((Submission.ChartBounds.frameVector_eq_zero_iff (I := I) (x₀ := z₀) (p := q)
        (by simpa using hqs) u).mp h))
  set p₀ : E × E := ((extChartAt I z₀) q, c • u) with hp₀def
  have hp₀O : p₀ ∈ D.O := hwO
  have hframe : frameVector (I := I) z₀ q u = w := hwdef.symm
  -- the chart geodesic of the flow, and its rescaling to the interval `(-2, 2)`
  have hgc0 : HasChartGeodesicOn cov z₀ q (frameVector (I := I) z₀ q (p₀).2)
      (fun s : ℝ => (D.α p₀ s).1) (fun s : ℝ => (D.α p₀ s).2) (-D.ρ) D.ρ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (D.α p₀ 0).1 = (extChartAt I z₀) q
      rw [D.h0 p₀ hp₀O]
    · show (D.α p₀ 0).2
        = (trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q
            (frameVector (I := I) z₀ q (p₀).2)
      rw [D.h0 p₀ hp₀O, clm_frameVector (I := I) hqs]
    · intro t ht
      exact D.htgt p₀ hp₀O t (le_of_lt (abs_lt.mpr ⟨ht.1, ht.2⟩))
    · intro t ht
      exact (D.hode p₀ hp₀O t (le_of_lt (abs_lt.mpr ⟨ht.1, ht.2⟩))).fst
    · intro t ht
      have h := D.hode p₀ hp₀O t (le_of_lt (abs_lt.mpr ⟨ht.1, ht.2⟩))
      rw [chartSpray_apply] at h
      exact h.snd
  have hgc : HasChartGeodesicOn cov z₀ q (c⁻¹ • frameVector (I := I) z₀ q (p₀).2)
      (fun s : ℝ => (D.α p₀ (c⁻¹ * s)).1) (fun s : ℝ => c⁻¹ • (D.α p₀ (c⁻¹ * s)).2)
      (-(2 : ℝ)) 2 := by
    have h := hgc0.const_smul (hr := inv_pos.mpr hcpos)
    have hA : -D.ρ / c⁻¹ = -(2 : ℝ) := by rw [neg_div, hρc]
    have hB : D.ρ / c⁻¹ = 2 := hρc
    rw [hA, hB] at h
    exact h
  -- the chart geodesic curve
  have hpt0 : (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * 0)).1) = q := by
    rw [mul_zero, D.h0 p₀ hp₀O, hp₀def]
    simp only [Prod.fst]
    exact (extChartAt I z₀).left_inv hqs
  have hvr : c⁻¹ • (D.α p₀ (c⁻¹ * 0)).2 = u := by
    rw [mul_zero, D.h0 p₀ hp₀O, hp₀def]
    simp only [Prod.snd]
    rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
  have hsub : Ioo (-1 : ℝ) (3 / 2) ⊆ Ioo (-(2 : ℝ)) 2 :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hγsm : ContMDiffOn 𝓘(ℝ) I ∞
      (fun s : ℝ => (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * s)).1)) (Ioo (-1 : ℝ) (3 / 2)) :=
    contMDiffOn_chartCurve_of_chartODE (cov := cov) z₀
      (fun s hs => hgc.2.2.1 s (hsub hs)) (fun s hs => hgc.2.2.2.1 s (hsub hs))
      (fun s hs => hgc.2.2.2.2 s (hsub hs))
  have hγgeo : ∀ t ∈ Ioo (-1 : ℝ) (3 / 2),
      IsGeodesicAt cov (fun s : ℝ => (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * s)).1)) t :=
    fun t ht => isGeodesicAt_of_chartODE (cov := cov) z₀ (by norm_num : (-1 : ℝ) < 3 / 2) ht
      (fun s hs => hgc.2.2.1 s (hsub hs)) (fun s hs => hgc.2.2.2.1 s (hsub hs))
      (fun s hs => hgc.2.2.2.2 s (hsub hs))
  have hγvel : curveVelocity (I := I)
      (fun s : ℝ => (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * s)).1)) 0
      = frameVector (I := I) z₀ q u := by
    have hvel0 := curveVelocity_chartCurve (I := I) (x₀ := z₀)
      (u := fun s : ℝ => (D.α p₀ (c⁻¹ * s)).1)
      (v := c⁻¹ • (D.α p₀ (c⁻¹ * 0)).2) (t := 0) (hgc.2.2.2.1 0 (by norm_num))
      (hgc.2.2.1 0 (by norm_num))
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-2) 2))
        (fun s hs => hgc.2.2.1 s hs))
    rw [hpt0] at hvel0
    exact hvel0.trans (by rw [hvr])
  -- non-vanishing of the velocity of the chart geodesic
  have hpos0 : 0 < chartGram (I := I) z₀ q (c • u) (c • u) := by
    have hu0 : chartGram (I := I) z₀ q u u = ‖w‖ ^ 2 := by
      rw [chartGram_apply, real_inner_self_eq_norm_sq, hframe]
    rw [chartGram_smul_fst, chartGram_smul_snd, hu0, ← mul_assoc, ← pow_two]
    positivity
  have hγne : ∀ t ∈ Ioo (-1 : ℝ) (3 / 2), curveVelocity (I := I)
      (fun s : ℝ => (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * s)).1)) t ≠ 0 := by
    intro t ht
    have ht2 : c⁻¹ * t ∈ Ioo (-D.ρ) D.ρ := by
      have hp1 : 0 < c⁻¹ := inv_pos.mpr hcpos
      have h1 : c⁻¹ * (-1) < c⁻¹ * t := mul_lt_mul_of_pos_left ht.1 hp1
      have h2 : c⁻¹ * t < c⁻¹ * (3 / 2) := mul_lt_mul_of_pos_left ht.2 hp1
      rw [hcinv] at h1 h2 ⊢
      exact mem_Ioo.mpr ⟨by linarith [h1, D.hρ], by linarith [h2, D.hρ]⟩
    have hconst := Submission.GeodesicGlobal2.chartGram_const_of_chartODE (cov := cov) hmet
      (x₀ := z₀) (u := fun s : ℝ => (D.α p₀ s).1) (w := fun s : ℝ => (D.α p₀ s).2)
      (fun s hs => hgc0.2.2.1 s hs) (fun s hs => hgc0.2.2.2.1 s hs)
      (fun s hs => hgc0.2.2.2.2 s hs) (t₀ := 0) ⟨by linarith [D.hρ], D.hρ⟩ (c⁻¹ * t) ht2
    have hval0 : chartGram (I := I) z₀ ((extChartAt I z₀).symm ((D.α p₀ 0).1)) ((D.α p₀ 0).2)
        ((D.α p₀ 0).2) = chartGram (I := I) z₀ q (c • u) (c • u) := by
      have h0 := D.h0 p₀ hp₀O
      rw [h0, hp₀def]
      simp only [Prod.fst, Prod.snd]
      rw [(extChartAt I z₀).left_inv hqs]
    have hne : (D.α p₀ (c⁻¹ * t)).2 ≠ 0 := by
      intro h0
      have hp := hconst.trans hval0
      rw [h0, Submission.ChartBounds.chartGram_zero] at hp
      exact absurd hp.symm (ne_of_gt hpos0)
    have hwco : c⁻¹ • (D.α p₀ (c⁻¹ * t)).2 ≠ 0 := smul_ne_zero (inv_ne_zero hcne) hne
    have hvel0 := curveVelocity_chartCurve (I := I) (x₀ := z₀)
      (u := fun s : ℝ => (D.α p₀ (c⁻¹ * s)).1)
      (v := c⁻¹ • (D.α p₀ (c⁻¹ * t)).2) (t := t) (hgc.2.2.2.1 t (hsub ht))
      (hgc.2.2.1 t (hsub ht))
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (hsub ht)) (fun s hs => hgc.2.2.1 s hs))
    rw [hvel0]
    exact fun hcon => hwco ((Submission.ChartBounds.frameVector_eq_zero_iff (I := I)
      (x₀ := z₀) (p := (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * t)).1))
      (mem_source_chartCurve (I := I) (x₀ := z₀)
        (u := fun s : ℝ => (D.α p₀ (c⁻¹ * s)).1) (t := t) (hgc.2.2.1 t (hsub ht)))
      (c⁻¹ • (D.α p₀ (c⁻¹ * t)).2)).mp hcon)
  -- the interval on which the two curves are compared
  have hgg : 0 < geodDelta (cov := cov) hmet := geodDelta_pos (cov := cov) hmet
  set a : ℝ := max (-1) (-(geodDelta (cov := cov) hmet / (2 * ‖w‖))) with hadef
  set b : ℝ := min (3 / 2) (1 + geodDelta (cov := cov) hmet / (2 * ‖w‖)) with hbdef
  have ha1 : -1 ≤ a := by rw [hadef]; exact le_max_left _ _
  have ha2 : a < 0 := by
    rw [hadef]
    exact max_lt (by norm_num) (by
      have : 0 < geodDelta (cov := cov) hmet / (2 * ‖w‖) := div_pos hgg (by positivity)
      linarith)
  have hb1 : b ≤ 3 / 2 := by rw [hbdef]; exact min_le_left _ _
  have hb2 : 1 < b := by
    rw [hbdef]
    exact lt_min (by norm_num) (by
      have : 0 < geodDelta (cov := cov) hmet / (2 * ‖w‖) := div_pos hgg (by positivity)
      linarith)
  have hab : Ioo a b ⊆ Ioo (-1 : ℝ) (3 / 2) :=
    fun s hs => ⟨by linarith [hs.1, ha1], by linarith [hs.2, hb1]⟩
  have hmemη : ∀ s ∈ Ioo a b,
      ‖w‖ * s ∈ Ioo (-(geodDelta (cov := cov) hmet))
        (‖w‖ + geodDelta (cov := cov) hmet) := by
    intro s hs
    have hsge : -(geodDelta (cov := cov) hmet / (2 * ‖w‖)) ≤ a := by
      rw [hadef]; exact le_max_right _ _
    have hsle : b ≤ 1 + geodDelta (cov := cov) hmet / (2 * ‖w‖) := by
      rw [hbdef]; exact min_le_right _ _
    have hwne : ‖w‖ ≠ 0 := ne_of_gt hwv
    refine mem_Ioo.mpr ⟨?_, ?_⟩
    · have h1 : -(geodDelta (cov := cov) hmet / (2 * ‖w‖)) * ‖w‖ ≤ a * ‖w‖ :=
        mul_le_mul_of_nonneg_right hsge (norm_nonneg w)
      have h2 : -(geodDelta (cov := cov) hmet / (2 * ‖w‖)) * ‖w‖
          = -(geodDelta (cov := cov) hmet / 2) := by
        field_simp
      have h3 : a * ‖w‖ < s * ‖w‖ := by
        rw [mul_comm a ‖w‖, mul_comm s ‖w‖]
        exact mul_lt_mul_of_pos_left hs.1 hwv
      calc -(geodDelta (cov := cov) hmet) < -(geodDelta (cov := cov) hmet / 2) := by linarith
        _ = -(geodDelta (cov := cov) hmet / (2 * ‖w‖)) * ‖w‖ := h2.symm
        _ ≤ a * ‖w‖ := h1
        _ < s * ‖w‖ := h3
        _ = ‖w‖ * s := by ring
    · have h1 : b * ‖w‖ ≤ (1 + geodDelta (cov := cov) hmet / (2 * ‖w‖)) * ‖w‖ :=
        mul_le_mul_of_nonneg_right hsle (norm_nonneg w)
      have h2 : (1 + geodDelta (cov := cov) hmet / (2 * ‖w‖)) * ‖w‖
          = ‖w‖ + geodDelta (cov := cov) hmet / 2 := by
        field_simp
      have h3 : s * ‖w‖ < b * ‖w‖ := by
        rw [mul_comm s ‖w‖, mul_comm b ‖w‖]
        exact mul_lt_mul_of_pos_left hs.2 hwv
      calc ‖w‖ * s = s * ‖w‖ := by ring
        _ < b * ‖w‖ := h3
        _ ≤ (1 + geodDelta (cov := cov) hmet / (2 * ‖w‖)) * ‖w‖ := h1
        _ = ‖w‖ + geodDelta (cov := cov) hmet / 2 := h2
        _ < ‖w‖ + geodDelta (cov := cov) hmet := by linarith
  -- the geodesic segment underlying `GExp q w`
  set ξ : TangentSpace I q := unitOf w (norm_pos_iff.mp hwv) with hξdef
  have hξnorm : ‖ξ‖ = 1 := unitOf_norm w (norm_pos_iff.mp hwv)
  have hηsm : ContMDiffOn 𝓘(ℝ) I ∞
      (fun s : ℝ => (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm) (‖w‖ * s))
      (Ioo a b) := by
    obtain ⟨-, -, hgcsm', -, -⟩ := geodCurve_spec (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm
    have hlin : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => ‖w‖ * s) (Ioo a b) :=
      (contMDiff_const.mul contMDiff_id).contMDiffOn
    exact hgcsm'.comp hlin hmemη
  have hηgeo : ∀ t ∈ Ioo a b,
      IsGeodesicAt cov (fun s : ℝ =>
        (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm) (‖w‖ * s)) t := by
    obtain ⟨-, -, hgcsm', hgcgeo', -⟩ := geodCurve_spec (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm
    intro t ht
    have hpre2 : (fun s : ℝ => ‖w‖ * s) ⁻¹'
        (Ioo (-(geodDelta (cov := cov) hmet)) (‖w‖ + geodDelta (cov := cov) hmet)) ∈ 𝓝 t :=
      (continuousAt_const.mul continuousAt_id).preimage_mem_nhds
        (IsOpen.mem_nhds isOpen_Ioo (hmemη t ht))
    have hmd : ∀ᶠ s in 𝓝 t,
        MDifferentiableAt 𝓘(ℝ) I (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm)
          (‖w‖ * s) := by
      filter_upwards [hpre2] with s hs
      exact (hgcsm'.contMDiffAt (IsOpen.mem_nhds isOpen_Ioo hs)).mdifferentiableAt (by simp)
    exact isGeodesicAt_comp_mul (cov := cov) (γ := geodCurve (cov := cov) hmet ‖w‖
      (norm_nonneg w) q ξ hξnorm) (c := ‖w‖) (t := t) (ne_of_gt hwv) hmd
      (hgcgeo' (‖w‖ * t) (hmemη t ht))
  have hηne : ∀ t ∈ Ioo a b, curveVelocity (I := I)
      (fun s : ℝ => (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm) (‖w‖ * s))
      t ≠ 0 := by
    obtain ⟨-, -, hgcsm', -, hgcspeed'⟩ := geodCurve_spec (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm
    intro t ht
    have hvelη : curveVelocity (I := I)
        (fun s : ℝ => (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm) (‖w‖ * s)) t
        = (‖w‖ : ℝ) • curveVelocity (I := I) (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w)
            q ξ hξnorm) (‖w‖ * t) :=
      curveVelocity_comp_mul (I := I)
        ((hgcsm'.contMDiffAt (IsOpen.mem_nhds isOpen_Ioo (hmemη t ht))).mdifferentiableAt
          (by simp))
    intro hzero
    have hnorm : ‖curveVelocity (I := I)
        (fun s : ℝ => (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm) (‖w‖ * s)) t‖
        = ‖w‖ := by
      rw [hvelη, norm_smul, Real.norm_eq_abs, abs_of_pos hwv,
        hgcspeed' (‖w‖ * t) (hmemη t ht), mul_one]
    rw [hzero, norm_zero] at hnorm
    exact (ne_of_gt hwv) hnorm.symm
  -- the initial data agree
  have hpt : (fun s : ℝ => (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * s)).1)) 0
      = (fun s : ℝ => (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm) (‖w‖ * s)) 0 := by
    obtain ⟨hgc0', -, -, -, -⟩ := geodCurve_spec (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm
    show (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * 0)).1)
      = (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm) (‖w‖ * 0)
    rw [hpt0, mul_zero]
    exact hgc0'.symm
  have hvel : curveVelocity (I := I)
      (fun s : ℝ => (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * s)).1)) 0
      = curveVelocity (I := I)
        (fun s : ℝ => (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm) (‖w‖ * s)) 0 := by
    have h2E : (curveVelocity (I := I)
        (fun s : ℝ => (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm) (‖w‖ * s)) 0 : E)
        = (w : E) := by
      obtain ⟨-, hgcv', hgcsm', -, -⟩ := geodCurve_spec (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm
      have hd : MDifferentiableAt 𝓘(ℝ) I (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ
          hξnorm) (‖w‖ * 0) :=
        (hgcsm'.contMDiffAt (IsOpen.mem_nhds isOpen_Ioo (hmemη 0 ⟨ha2, by linarith [hb2]⟩))).mdifferentiableAt
          (by simp)
      have hcomp : (curveVelocity (I := I)
          (fun s : ℝ => (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm) (‖w‖ * s)) 0 : E)
          = (fun z : E => (‖w‖ : ℝ) • z) (curveVelocity (I := I) (geodCurve (cov := cov) hmet
              ‖w‖ (norm_nonneg w) q ξ hξnorm) (‖w‖ * 0) : E) :=
        curveVelocity_comp_mul (I := I) hd
      have hb : (curveVelocity (I := I) (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ
          hξnorm) (‖w‖ * 0) : E) = (ξ : E) := by
        have h1 := congrArg (fun r : ℝ => (curveVelocity (I := I) (geodCurve (cov := cov) hmet
          ‖w‖ (norm_nonneg w) q ξ hξnorm) r : E)) (mul_zero ‖w‖)
        rw [h1]
        exact hgcv'
      have hsmT : (‖w‖ : ℝ) • ξ = w := by
        rw [hξdef, unitOf, smul_smul, mul_inv_cancel₀ (ne_of_gt hwv), one_smul]
      exact hcomp.trans ((congrArg (fun z : E => (‖w‖ : ℝ) • z) hb).trans hsmT)
    have h1E : (curveVelocity (I := I)
        (fun s : ℝ => (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * s)).1)) 0 : E)
        = (frameVector (I := I) z₀ q u : E) := hγvel
    have h2E' : (w : E) = (frameVector (I := I) z₀ q u : E) := by rw [hframe]
    exact h1E.trans (h2E'.symm.trans h2E.symm)
  have hEqOn := eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) (a := a) (b := b)
    (hγsm.mono hab) (hηsm) (fun t ht => hγgeo t (hab ht)) hηgeo
    (fun t ht => hγne t (hab ht)) hηne
    (⟨ha2, by linarith [hb2]⟩ : (0 : ℝ) ∈ Ioo a b) hpt hvel
  have hval1 : (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * 1)).1)
      = (geodCurve (cov := cov) hmet ‖w‖ (norm_nonneg w) q ξ hξnorm) (‖w‖ * 1) :=
    hEqOn (⟨by linarith [ha2], hb2⟩ : (1 : ℝ) ∈ Ioo a b)
  rw [mul_one, mul_one] at hval1
  have hfinal : GExp (cov := cov) hmet q w
      = (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * 1)).1) := by
    rw [GExp_apply (cov := cov) hmet (norm_pos_iff.mp hwv), mul_one, ← hval1]
  rw [hwdef] at hfinal
  rw [mul_one] at hfinal
  exact hfinal.trans (by rw [hp₀def])

end Ident

/-! ## The uniform Rauch bound for the chart-flow exponential map -/

section Bound

variable [Nontrivial E] [CompactSpace M]
variable {z₀ : M} {Z : Set M}

/-- The **chart-flow exponential map** attached to the flow data `D`: the time-`c⁻¹` value of the
flow of the chart spray, read back through the chart.  By `GExp_eq_chartFlow` it agrees with
`u ↦ GExp q (frameVector z₀ q u)` whenever the phase is in the flow domain `D.O`. -/
noncomputable def chartFlowExp (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (q : M) : E → M :=
  fun u => (extChartAt I z₀).symm
    ((D.α ((extChartAt I z₀) q, flowScale D • u) (flowScale D)⁻¹).1)

lemma chartFlowExp_apply (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (q : M) (u : E) :
    chartFlowExp (cov := cov) D q u = (extChartAt I z₀).symm
      ((D.α ((extChartAt I z₀) q, flowScale D • u) (flowScale D)⁻¹).1) := rfl

/-- **Smoothness of the chart-flow exponential map** at a point whose phase lies in the flow
domain. -/
lemma chartFlowExp_contMDiffAt (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {q : M}
    {u : E} (hK : ((extChartAt I z₀) q, flowScale D • u) ∈ chartData (I := I) z₀ Z) :
    ContMDiffAt 𝓘(ℝ, E) I ∞ (chartFlowExp (cov := cov) D q) u := by
  set c : ℝ := flowScale D with hcdef
  have hcinv : c⁻¹ = D.ρ / 2 := by rw [hcdef]; exact inv_flowScale D
  have hO : ((extChartAt I z₀) q, c • u) ∈ D.O := D.hKO hK
  have hjoint := D.hjoint (((extChartAt I z₀) q, c • u)) hK (c⁻¹)
    (by rw [hcinv, abs_of_pos (div_pos D.hρ two_pos)]; linarith [D.hρ])
  have hmapsm : ContDiffAt ℝ ∞ (fun v : E => ((extChartAt I z₀) q, c • v)) u :=
    contDiffAt_const.prodMk (contDiffAt_const.smul contDiffAt_id)
  have hinner : ContDiffAt ℝ ∞ (fun v : E => (((extChartAt I z₀) q, c • v), c⁻¹)) u :=
    hmapsm.prodMk (contDiffAt_const (c := c⁻¹))
  have hcomp : ContDiffAt ℝ ∞ (fun v : E => D.α ((extChartAt I z₀) q, c • v) (c⁻¹)) u := by
    have h := ContDiffAt.comp (x := u) hjoint hinner
    simpa [Function.comp_def] using h
  have hcomp2 : ContDiffAt ℝ ∞ (fun v : E => (D.α ((extChartAt I z₀) q, c • v) (c⁻¹)).1) u :=
    hcomp.fst
  have hmem : (D.α ((extChartAt I z₀) q, c • u) (c⁻¹)).1 ∈ (extChartAt I z₀).target :=
    D.htgt (((extChartAt I z₀) q, c • u)) hO (c⁻¹)
      (by rw [hcinv, abs_of_pos (div_pos D.hρ two_pos)]; linarith [D.hρ])
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I z₀).symm
      ((D.α ((extChartAt I z₀) q, c • u) (c⁻¹)).1) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) z₀).contMDiffAt
      ((isOpen_extChartAt_target z₀).mem_nhds hmem)
  have hres := hsymm.comp u (hcomp2.contMDiffAt)
  have hfun : chartFlowExp (cov := cov) D q
      = fun v : E => (extChartAt I z₀).symm ((D.α ((extChartAt I z₀) q, c • v) (c⁻¹)).1) := rfl
  rw [hfun]
  exact hres

/-- **The uniform Rauch bound for the chart-flow exponential map.**  Let `D` be the flow data of
the chart at `z₀` for a compact piece `Z ⊆ (chartAt H z₀).source`, let `λ > 0` bound the chart
metric at the points of `Z` from below, and let `q ∈ Z`.  Then, for every coordinate velocity `u`
of small chart length `√(chartGram z₀ q u u)`, the differential of the chart-flow exponential map
satisfies Rauch's bound on the orthogonal complement of `u`:

`‖(d chartFlowExp_q)_u x‖ ≤ (sin ‖u‖/‖u‖) · ‖x‖`,

all metric quantities being the chart metric at `z₀` based at `q`. -/
theorem exists_uniform_chartFlow_rauch_bound_of_data
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (hZsrc : Z ⊆ (chartAt H z₀).source)
    {lam : ℝ} (hlam : 0 < lam)
    (hlam_bnd : ∀ q ∈ Z, ∀ w : E, lam * ‖w‖ ^ 2 ≤ chartGram (I := I) z₀ q w w)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ Z, ∀ u x : E,
      0 < Real.sqrt (chartGram (I := I) z₀ q u u) →
      Real.sqrt (chartGram (I := I) z₀ q u u) < ρ →
      chartGram (I := I) z₀ q u x = 0 →
      ‖(mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) x‖
        ≤ (Real.sin (Real.sqrt (chartGram (I := I) z₀ q u u))
            / Real.sqrt (chartGram (I := I) z₀ q u u))
          * Real.sqrt (chartGram (I := I) z₀ q x x) := by
  classical
  have hcpos : 0 < flowScale D := flowScale_pos D
  have hcinvpos : 0 < (flowScale D)⁻¹ := inv_pos.mpr hcpos
  have hsqlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  refine ⟨min (Real.sqrt lam * (flowScale D)⁻¹) (Real.pi / 3),
    lt_min (mul_pos hsqlam hcinvpos) (by linarith [Real.pi_pos]), ?_⟩
  intro q hq u x hu_pos hu_lt hu_orth
  have hqs : q ∈ (extChartAt I z₀).source := by simpa using hZsrc hq
  have hu_lt2 : Real.sqrt (chartGram (I := I) z₀ q u u) < Real.pi / 3 :=
    lt_of_lt_of_le hu_lt (min_le_right _ _)
  set c : ℝ := flowScale D with hcdef
  have hcpos' : 0 < c := by rw [hcdef]; exact hcpos
  have hcne : c ≠ 0 := ne_of_gt hcpos'
  have hcinv : c⁻¹ = D.ρ / 2 := by rw [hcdef]; exact inv_flowScale D
  -- the chart size of the coordinate velocity
  have huc : c * ‖u‖ < 1 := by
    have h1 : lam * ‖u‖ ^ 2 ≤ chartGram (I := I) z₀ q u u := hlam_bnd q hq u
    have h2 : Real.sqrt lam * ‖u‖ ≤ Real.sqrt (chartGram (I := I) z₀ q u u) := by
      rw [← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul hlam.le]
      exact Real.sqrt_le_sqrt h1
    have h3 : c * ‖u‖ ≤ c * (Real.sqrt (chartGram (I := I) z₀ q u u) / Real.sqrt lam) := by
      refine mul_le_mul_of_nonneg_left ?_ hcpos'.le
      rw [le_div_iff₀ hsqlam, mul_comm]
      exact h2
    refine lt_of_le_of_lt h3 ?_
    calc c * (Real.sqrt (chartGram (I := I) z₀ q u u) / Real.sqrt lam)
        < c * ((Real.sqrt lam * c⁻¹) / Real.sqrt lam) :=
          mul_lt_mul_of_pos_left (div_lt_div_of_pos_right
            (lt_of_lt_of_le hu_lt (min_le_left _ _)) hsqlam) hcpos'
      _ = 1 := by
          have h4 : c * ((Real.sqrt lam * c⁻¹) / Real.sqrt lam)
              = (c * c⁻¹) * (Real.sqrt lam / Real.sqrt lam) := by ring
          rw [h4, mul_inv_cancel₀ hcne, div_self (ne_of_gt hsqlam), mul_one]
  -- the phase of the flow
  set p₀ : E × E := ((extChartAt I z₀) q, c • u) with hp₀def
  have hp₀K : p₀ ∈ chartData (I := I) z₀ Z :=
    ⟨⟨q, hq, rfl⟩, by
      rw [mem_closedBall, dist_zero_right, hp₀def]
      simp only [Prod.snd, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos']
      exact huc.le⟩
  have hp₀O : p₀ ∈ D.O := D.hKO hp₀K
  -- the one-parameter family of phases
  set pt : ℝ → E × E := fun t => ((extChartAt I z₀) q, c • (u + t • x)) with hptdef
  set hδ0 : ℝ := min (1:ℝ) ((1 - c * ‖u‖) / (2 * (1 + c * ‖x‖))) with hδ0def
  have hδ0pos : 0 < hδ0 := by
    rw [hδ0def]
    exact lt_min one_pos (div_pos (by linarith [huc]) (by positivity))
  have hδ0le : hδ0 ≤ 1 := by rw [hδ0def]; exact min_le_left _ _
  have hmem1 : ∀ t ∈ Ioo (-hδ0) hδ0, t ∈ Icc (-1 : ℝ) 1 :=
    fun t ht => ⟨by linarith [ht.1, hδ0le], by linarith [ht.2, hδ0le]⟩
  have hpt0eq : pt 0 = p₀ := by
    rw [hptdef, hp₀def]
    simp only [zero_smul, add_zero]
  have hptK : ∀ t ∈ Ioo (-hδ0) hδ0, pt t ∈ chartData (I := I) z₀ Z := by
    intro t ht
    rw [hptdef]
    refine ⟨⟨q, hq, rfl⟩, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    simp only [Prod.snd, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos']
    have htab : |t| < hδ0 := abs_lt.mpr ⟨ht.1, ht.2⟩
    have ht2 : |t| < (1 - c * ‖u‖) / (2 * (1 + c * ‖x‖)) :=
      lt_of_lt_of_le htab (by rw [hδ0def]; exact min_le_right _ _)
    have h1 : c * ‖u + t • x‖ ≤ c * (‖u‖ + |t| * ‖x‖) := by
      refine mul_le_mul_of_nonneg_left ?_ hcpos'.le
      calc ‖u + t • x‖ ≤ ‖u‖ + ‖t • x‖ := norm_add_le _ _
        _ = ‖u‖ + |t| * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h3 : |t| * ‖x‖ ≤ (1 - c * ‖u‖) / (2 * (1 + c * ‖x‖)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right ht2.le (norm_nonneg x)
    have h4 : c * ((1 - c * ‖u‖) / (2 * (1 + c * ‖x‖)) * ‖x‖) ≤ (1 - c * ‖u‖) / 2 := by
      have h4a : c * ((1 - c * ‖u‖) / (2 * (1 + c * ‖x‖)) * ‖x‖)
          = c * (1 - c * ‖u‖) * ‖x‖ / (2 * (1 + c * ‖x‖)) := by ring
      rw [h4a, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [norm_nonneg x, hcpos'.le, huc]
    have h5 : c * (|t| * ‖x‖) ≤ (1 - c * ‖u‖) / 2 := by
      have h6 := mul_le_mul_of_nonneg_left h3 hcpos'.le
      have h6' : c * ((1 - c * ‖u‖) / (2 * (1 + c * ‖x‖)) * ‖x‖)
          = c * ((1 - c * ‖u‖) / (2 * (1 + c * ‖x‖))) * ‖x‖ := by ring
      linarith [h6, h4, h6']
    have h7 : c * (‖u‖ + |t| * ‖x‖) ≤ c * ‖u‖ + (1 - c * ‖u‖) / 2 := by
      have h8 : c * (‖u‖ + |t| * ‖x‖) = c * ‖u‖ + c * (|t| * ‖x‖) := by ring
      rw [h8]
      linarith [h5]
    have h9 : c * ‖u‖ + (1 - c * ‖u‖) / 2 < 1 := by linarith [huc]
    linarith [h1, h7, h9]
  have hptO : ∀ t ∈ Ioo (-hδ0) hδ0, pt t ∈ D.O := fun t ht => D.hKO (hptK t ht)
  set Φ : ℝ × ℝ → E × E :=
    fun p' => ((D.α (pt p'.2) (c⁻¹ * p'.1)).1, c⁻¹ • (D.α (pt p'.2) (c⁻¹ * p'.1)).2) with hΦdef
  -- the chart geodesic of the family at `t = 0`, with velocity `frameVector z₀ q u`
  have hgc : HasChartGeodesicOn cov z₀ q (frameVector (I := I) z₀ q u) (gc Φ) (gv Φ)
      (-(2 : ℝ)) 2 := by
    have hsub : ∀ s ∈ Ioo (-(2 : ℝ)) 2, c⁻¹ * s ∈ Ioo (-D.ρ) D.ρ := by
      intro s hs
      have hs2 : |s| < 2 := abs_lt.mpr ⟨hs.1, hs.2⟩
      have hlt : |c⁻¹ * s| < D.ρ := by
        rw [abs_mul, abs_of_pos hcinvpos, hcinv]
        nlinarith [abs_nonneg s, D.hρ, hs2]
      exact mem_Ioo.mpr (abs_lt.mp hlt)
    have hpt0O : pt 0 ∈ D.O := hptO 0 ⟨by linarith [hδ0pos], by linarith [hδ0pos]⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (D.α (pt 0) (c⁻¹ * 0)).1 = (extChartAt I z₀) q
      rw [mul_zero, D.h0 (pt 0) hpt0O, hptdef]
    · show c⁻¹ • (D.α (pt 0) (c⁻¹ * 0)).2
          = (trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q
              (frameVector (I := I) z₀ q u)
      rw [clm_frameVector (I := I) hqs, mul_zero, D.h0 (pt 0) hpt0O, hptdef]
      simp only [Prod.snd, smul_smul, inv_mul_cancel₀ hcne, one_smul, zero_smul, add_zero]
    · intro s hs
      exact D.htgt (pt 0) hpt0O (c⁻¹ * s)
        (le_of_lt (abs_lt.mpr ⟨(hsub s hs).1, (hsub s hs).2⟩))
    · intro s hs
      have hφ : HasDerivAt (fun s' : ℝ => c⁻¹ * s') c⁻¹ s := by
        simpa using (hasDerivAt_id s).const_mul c⁻¹
      have h1 := (Submission.Gauss.hasDerivAt_fst (D.hode (pt 0) hpt0O (c⁻¹ * s)
        (le_of_lt (abs_lt.mpr ⟨(hsub s hs).1, (hsub s hs).2⟩)))).scomp s hφ
      have h1' : HasDerivAt (fun s' : ℝ => (D.α (pt 0) (c⁻¹ * s')).1)
          (c⁻¹ • (D.α (pt 0) (c⁻¹ * s)).2) s := by
        simpa [Function.comp_def] using h1
      show HasDerivAt (fun s' : ℝ => (D.α (pt 0) (c⁻¹ * s')).1)
        (c⁻¹ • (D.α (pt 0) (c⁻¹ * s)).2) s
      exact h1'
    · intro s hs
      have htgt := D.htgt (pt 0) hpt0O (c⁻¹ * s)
        (le_of_lt (abs_lt.mpr ⟨(hsub s hs).1, (hsub s hs).2⟩))
      have hφ : HasDerivAt (fun s' : ℝ => c⁻¹ * s') c⁻¹ s := by
        simpa using (hasDerivAt_id s).const_mul c⁻¹
      have h1 : HasDerivAt (fun s' : ℝ => (D.α (pt 0) (c⁻¹ * s')).2)
          (c⁻¹ • chartGeodesicVectorField cov z₀ (D.α (pt 0) (c⁻¹ * s))) s := by
        have h := (Submission.Gauss.hasDerivAt_snd (D.hode (pt 0) hpt0O (c⁻¹ * s)
          (le_of_lt (abs_lt.mpr ⟨(hsub s hs).1, (hsub s hs).2⟩)))).scomp s hφ
        simpa [Function.comp_def, chartSpray_apply] using h
      have h2 := h1.const_smul c⁻¹
      have hpair : (gc Φ s, gv Φ s)
          = ((D.α (pt 0) (c⁻¹ * s)).1, c⁻¹ • (D.α (pt 0) (c⁻¹ * s)).2) := by
        rw [hΦdef]
        rfl
      have hsm := chartGeodesicVectorField_smul cov z₀ c⁻¹ (D.α (pt 0) (c⁻¹ * s)) htgt
      show HasDerivAt (fun s' : ℝ => c⁻¹ • (D.α (pt 0) (c⁻¹ * s')).2)
          (chartGeodesicVectorField cov z₀ (gc Φ s, gv Φ s)) s
      rw [hpair, hsm, pow_two, ← smul_smul]
      exact h2
  -- the Jacobi tensor along it
  obtain ⟨Y, U, hY0, hU0, hY, hU⟩ :=
    exists_jacobiSystemOn (cov := cov) htor hgc (by norm_num : (-(3 / 2) : ℝ) < 3 / 2)
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (by norm_num : (0 : ℝ) ∈ Icc (-(3 / 2)) (3 / 2))
  -- the constancy of the chart speed
  have hspeed : ∀ t ∈ Ioo (-(2 : ℝ)) 2,
      chartGram (I := I) z₀ ((extChartAt I z₀).symm ((D.α (pt 0) (c⁻¹ * t)).1))
        (c⁻¹ • (D.α (pt 0) (c⁻¹ * t)).2) (c⁻¹ • (D.α (pt 0) (c⁻¹ * t)).2)
        = chartGram (I := I) z₀ q u u := by
    intro t ht
    have h := Submission.GeodesicGlobal2.chartGram_const_of_chartODE (cov := cov) hmet
      (x₀ := z₀) (u := fun s : ℝ => (D.α (pt 0) (c⁻¹ * s)).1)
      (w := fun s : ℝ => c⁻¹ • (D.α (pt 0) (c⁻¹ * s)).2)
      (fun s hs => hgc.2.2.1 s hs) (fun s hs => hgc.2.2.2.1 s hs)
      (fun s hs => hgc.2.2.2.2 s hs) (t₀ := 0) (by norm_num) t ht
    have h0 : chartGram (I := I) z₀ ((extChartAt I z₀).symm ((D.α (pt 0) (c⁻¹ * 0)).1))
        (c⁻¹ • (D.α (pt 0) (c⁻¹ * 0)).2) (c⁻¹ • (D.α (pt 0) (c⁻¹ * 0)).2)
        = chartGram (I := I) z₀ q u u := by
      have hpt : (extChartAt I z₀).symm ((D.α (pt 0) (c⁻¹ * 0)).1) = q := by
        rw [mul_zero, D.h0 (pt 0) (hptO 0 ⟨by linarith [hδ0pos], by linarith [hδ0pos]⟩), hptdef]
        simp only [Prod.fst]
        exact (extChartAt I z₀).left_inv hqs
      have hvel : c⁻¹ • (D.α (pt 0) (c⁻¹ * 0)).2 = u := by
        rw [mul_zero, D.h0 (pt 0) (hptO 0 ⟨by linarith [hδ0pos], by linarith [hδ0pos]⟩), hptdef]
        simp only [Prod.snd, smul_smul, inv_mul_cancel₀ hcne, one_smul, zero_smul, add_zero]
      rw [hpt, hvel]
    rw [h]
    exact h0
  -- Rauch
  have hrauch := rauch_bound_arbitrary_base (cov := cov) hmet htor hpinch hqs hgc hspeed
    (c := Real.sqrt (chartGram (I := I) z₀ q u u)) hu_pos
    (Real.sq_sqrt (Submission.Minimal.chartGram_self_nonneg (I := I) z₀ q u)) hu_lt2
    (fun t ht => hY t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (fun t ht => hU t ⟨by linarith [ht.1], by linarith [ht.2]⟩) hY0 hU0 hu_orth
  -- the variation lemma
  have hΦ0 : ∀ t ∈ Ioo (-hδ0) hδ0, (Φ (0, t)).1 = (extChartAt I z₀) q := by
    intro t ht
    show (D.α (pt t) (c⁻¹ * 0)).1 = (extChartAt I z₀) q
    rw [mul_zero, D.h0 (pt t) (hptO t ht), hptdef]
  have hΦv : ∀ t ∈ Ioo (-hδ0) hδ0, (Φ (0, t)).2 = u + t • x := by
    intro t ht
    show c⁻¹ • (D.α (pt t) (c⁻¹ * 0)).2 = u + t • x
    rw [mul_zero, D.h0 (pt t) (hptO t ht), hptdef]
    simp only [Prod.snd, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  have hΦTGT : ∀ t ∈ Ioo (-hδ0) hδ0, ∀ s ∈ Ioo (-2 : ℝ) 2,
      (Φ (s, t)).1 ∈ (extChartAt I z₀).target := by
    intro t ht s hs
    refine D.htgt (pt t) (hptO t ht) (c⁻¹ * s) ?_
    rw [abs_mul, abs_of_pos hcinvpos, hcinv]
    have hs2 : |s| < 2 := abs_lt.mpr ⟨hs.1, hs.2⟩
    nlinarith [D.hρ, abs_nonneg s]
  have hΦODE : ∀ t ∈ Ioo (-hδ0) hδ0, ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov z₀ (Φ (s, t))) s := by
    intro t ht s hs
    have hsub' : ∀ s' ∈ Ioo (-(2 : ℝ)) 2, c⁻¹ * s' ∈ Ioo (-D.ρ) D.ρ := by
      intro s' hs'
      have hs2 : |s'| < 2 := abs_lt.mpr ⟨hs'.1, hs'.2⟩
      have hlt : |c⁻¹ * s'| < D.ρ := by
        rw [abs_mul, abs_of_pos hcinvpos, hcinv]
        nlinarith [abs_nonneg s', D.hρ, hs2]
      exact mem_Ioo.mpr (abs_lt.mp hlt)
    have hφ : HasDerivAt (fun s' : ℝ => c⁻¹ * s') c⁻¹ s := by
      simpa using (hasDerivAt_id s).const_mul c⁻¹
    have h1 := (Submission.Gauss.hasDerivAt_fst (D.hode (pt t) (hptO t ht) (c⁻¹ * s)
      (le_of_lt (abs_lt.mpr ⟨(hsub' s hs).1, (hsub' s hs).2⟩)))).scomp s hφ
    have h1' : HasDerivAt (fun s' : ℝ => (D.α (pt t) (c⁻¹ * s')).1)
        (c⁻¹ • (D.α (pt t) (c⁻¹ * s)).2) s := by
      simpa [Function.comp_def] using h1
    have htgt := D.htgt (pt t) (hptO t ht) (c⁻¹ * s)
      (le_of_lt (abs_lt.mpr ⟨(hsub' s hs).1, (hsub' s hs).2⟩))
    have h2 := (Submission.Gauss.hasDerivAt_snd (D.hode (pt t) (hptO t ht) (c⁻¹ * s)
      (le_of_lt (abs_lt.mpr ⟨(hsub' s hs).1, (hsub' s hs).2⟩)))).scomp s hφ
    have h2' : HasDerivAt (fun s' : ℝ => c⁻¹ • (D.α (pt t) (c⁻¹ * s')).2)
        (c⁻¹ • c⁻¹ • chartGeodesicVectorField cov z₀ (D.α (pt t) (c⁻¹ * s))) s := by
      have h2a : HasDerivAt (fun s' : ℝ => (D.α (pt t) (c⁻¹ * s')).2)
          (c⁻¹ • chartGeodesicVectorField cov z₀ (D.α (pt t) (c⁻¹ * s))) s :=
        h2.congr_of_eventuallyEq (by filter_upwards with y; rfl)
      exact (h2a.const_smul c⁻¹).congr_deriv rfl
    have hpair : Φ (s, t)
        = ((D.α (pt t) (c⁻¹ * s)).1, c⁻¹ • (D.α (pt t) (c⁻¹ * s)).2) := by
      rw [hΦdef]
    have h4 : chartGeodesicVectorField cov z₀ ((D.α (pt t) (c⁻¹ * s)).1,
        c⁻¹ • (D.α (pt t) (c⁻¹ * s)).2)
        = c⁻¹ • c⁻¹ • chartGeodesicVectorField cov z₀ (D.α (pt t) (c⁻¹ * s)) := by
      simpa [pow_two, smul_smul] using
        chartGeodesicVectorField_smul cov z₀ c⁻¹ (D.α (pt t) (c⁻¹ * s)) htgt
    rw [hpair, h4]
    exact h1'.prodMk h2'
  have hΦSM : ∀ s ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p' : ℝ × ℝ => Φ p') (s, 0) := by
    intro s hs
    have hsρ : |c⁻¹ * s| < D.ρ := by
      rw [abs_mul, abs_of_pos hcinvpos, hcinv]
      have hs2 : |s| < 2 := abs_lt.mpr ⟨hs.1, hs.2⟩
      nlinarith [D.hρ, abs_nonneg s]
    have hjoint := D.hjoint (pt 0) (hptK 0 ⟨by linarith [hδ0pos], by linarith [hδ0pos]⟩)
      (c⁻¹ * s) hsρ
    have hinner : ContDiffAt ℝ ∞ (fun p' : ℝ × ℝ => (pt p'.2, c⁻¹ * p'.1)) (s, 0) := by
      have h1 : ContDiffAt ℝ ∞ (fun p' : ℝ × ℝ =>
          (((extChartAt I z₀) q, c • (u + p'.2 • x)), c⁻¹ * p'.1)) (s, 0) := by fun_prop
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards with p'
      rw [hptdef]
    have h1 := hjoint.comp (s, 0) hinner
    have hpair := h1.fst.prodMk (h1.snd.const_smul c⁻¹)
    refine hpair.congr_of_eventuallyEq ?_
    filter_upwards with p'
    rfl
  have hΦstay : ∀ s ∈ Ioo (-2 : ℝ) 2, (gc Φ) s ∈ (extChartAt I z₀).target :=
    fun s hs => hgc.2.2.1 s hs
  have hΦu0 : ∀ s ∈ Ioo (-2 : ℝ) 2, HasDerivAt (gc Φ) (gv Φ s) s :=
    fun s hs => hgc.2.2.2.1 s hs
  have hΦw0 : ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (gv Φ) (chartGeodesicVectorField cov z₀ (gc Φ s, gv Φ s)) s :=
    fun s hs => hgc.2.2.2.2 s hs
  have hΦEXP : ∀ t ∈ Ioo (-hδ0) hδ0,
      chartFlowExp (cov := cov) D q (u + t • x) = (extChartAt I z₀).symm ((Φ (1, t)).1) := by
    intro t ht
    rw [chartFlowExp_apply, ← hcdef]
    simp only [hΦdef, hptdef, Prod.fst, mul_one]
  have hfd := mfderiv_of_eq_chartFlow (cov := cov) htor (δ := hδ0) (Φ := Φ)
    (f := chartFlowExp (cov := cov) D q) (v := u) (x := x) hδ0pos hΦ0 hΦv hΦTGT hΦODE hΦSM
    hΦstay hΦu0 hΦw0 hΦEXP
    ((chartFlowExp_contMDiffAt (cov := cov) D hp₀K).mdifferentiableAt (by simp))
    (fun t (ht : t ∈ Icc (-1 : ℝ) 1) => hY t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (fun t (ht : t ∈ Icc (-1 : ℝ) 1) => hU t ⟨by linarith [ht.1], by linarith [ht.2]⟩) hY0 hU0
  have hgram_self : ∀ a : E, Real.sqrt (chartGram (I := I) z₀ q a a) ^ 2
      = chartGram (I := I) z₀ q a a :=
    fun a => Real.sq_sqrt (Submission.Minimal.chartGram_self_nonneg (I := I) z₀ q a)
  have hkey : chartGram (I := I) z₀ ((extChartAt I z₀).symm ((D.α (pt 0) (c⁻¹ * 1)).1))
      ((Y 1) x) ((Y 1) x) = chartGram (I := I) z₀ (chartFlowExp (cov := cov) D q u)
        ((Y 1) x) ((Y 1) x) := by
    rw [chartFlowExp_apply, hptdef, ← hcdef]
    simp only [Prod.fst, mul_one, zero_smul, add_zero]
  have hnorm : ‖(mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) x‖ ^ 2
      = chartGram (I := I) z₀ (chartFlowExp (cov := cov) D q u) ((Y 1) x) ((Y 1) x) := by
    rw [hfd, chartGram_apply, real_inner_self_eq_norm_sq]
  have hchain : ‖(mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) x‖ ^ 2
      ≤ Real.sin (Real.sqrt (chartGram (I := I) z₀ q u u)) ^ 2
        * ((Real.sqrt (chartGram (I := I) z₀ q u u))⁻¹ ^ 2
            * chartGram (I := I) z₀ q x x) := by
    rw [hnorm, ← hkey]
    exact hrauch
  have hsin : 0 ≤ Real.sin (Real.sqrt (chartGram (I := I) z₀ q u u)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (Real.sqrt_nonneg _) (by linarith [hu_lt2, Real.pi_pos])
  have hYs : 0 ≤ Real.sin (Real.sqrt (chartGram (I := I) z₀ q u u))
      / Real.sqrt (chartGram (I := I) z₀ q u u) * Real.sqrt (chartGram (I := I) z₀ q x x) :=
    mul_nonneg (div_nonneg hsin (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine le_of_sq_le_sq ?_ hYs
  calc ‖(mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) x‖ ^ 2
      ≤ Real.sin (Real.sqrt (chartGram (I := I) z₀ q u u)) ^ 2
        * ((Real.sqrt (chartGram (I := I) z₀ q u u))⁻¹ ^ 2
            * chartGram (I := I) z₀ q x x) := hchain
    _ = (Real.sin (Real.sqrt (chartGram (I := I) z₀ q u u))
          / Real.sqrt (chartGram (I := I) z₀ q u u)
          * Real.sqrt (chartGram (I := I) z₀ q x x)) ^ 2 := by
        rw [mul_pow, div_pow, hgram_self u, inv_pow, hgram_self u, hgram_self x]
        ring

/-! ## Existence of the flow data from the uniform flow theorem of the commons -/

/-- The compact set of initial data attached to a compact piece of a chart is compact. -/
lemma isCompact_chartData {Z : Set M} (hZ : IsCompact Z)
    (hZsrc : Z ⊆ (chartAt H z₀).source) :
    IsCompact (chartData (I := I) z₀ Z) := by
  have hsub : Z ⊆ (extChartAt I z₀).source := fun q hq => by simpa using hZsrc hq
  exact (hZ.image_of_continuousOn ((continuousOn_extChartAt (I := I) z₀).mono hsub)).prod
    (isCompact_closedBall (0 : E) 1)

/-- **The flow data of a compact piece of a chart.**  For a compact `Z ⊆ (chartAt H z₀).source`
there is a flow datum `D : ChartFlowData z₀ Z`; it is produced by the uniform flow theorem
`Commons.Analysis.ODE.uniform_flow_joint` applied to the chart spray. -/
theorem exists_chartFlowData {Z : Set M} (hZ : IsCompact Z)
    (hZsrc : Z ⊆ (chartAt H z₀).source) :
    ∃ D : ChartFlowData (cov := cov) (I := I) z₀ Z, True := by
  obtain ⟨ρ, hρ, O, hO, hKO, hOW, α, h0, hode, hconn, hjoint, huniq⟩ :=
    Commons.Analysis.ODE.uniform_flow_joint (F := chartSpray (cov := cov) z₀)
      (W := (extChartAt I z₀).target ×ˢ (univ : Set E))
      ((isOpen_extChartAt_target z₀).prod isOpen_univ)
      (contDiffOn_chartSpray (cov := cov) z₀)
      (isCompact_chartData (z₀ := z₀) hZ hZsrc)
      (fun p hp => by
        obtain ⟨q, hq, hqeq⟩ := hp.1
        refine ⟨?_, trivial⟩
        rw [← hqeq]
        exact (extChartAt I z₀).map_source (by simpa using hZsrc hq))
  exact ⟨{ ρ := ρ
           hρ := hρ
           O := O
           hO := hO
           hKO := hKO
           hOW := hOW
           α := α
           h0 := h0
           hode := hode
           htgt := fun p hp t ht => (hconn p hp t ht).1
           hjoint := hjoint
           huniq := huniq }, trivial⟩

/-- A uniform bound on the coordinate vectors whose phase lies in the flow domain: the phase of
`u` (with chart velocity `flowScale D • u`) belongs to `O` as soon as `‖u‖` is small enough. -/
theorem exists_pos_phase_mem {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) :
    ∃ η : ℝ, 0 < η ∧ ∀ q ∈ Z, ∀ u : E, ‖u‖ ≤ η →
      ((extChartAt I z₀) q, flowScale D • u) ∈ D.O := by
  have hcpos : 0 < flowScale D := flowScale_pos D
  refine ⟨1 / (2 * flowScale D), by positivity, fun q hq u hu => D.hKO ?_⟩
  refine ⟨⟨q, hq, rfl⟩, ?_⟩
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (flowScale_pos D)]
  have hc : flowScale D ≠ 0 := flowScale_ne_zero D
  have h1 : flowScale D * (1 / (2 * flowScale D)) = 1 / 2 := by field_simp
  calc flowScale D * ‖u‖ ≤ flowScale D * (1 / (2 * flowScale D)) :=
        mul_le_mul_of_nonneg_left hu (flowScale_pos D).le
    _ = 1 / 2 := h1
    _ ≤ 1 := by norm_num

end Bound
