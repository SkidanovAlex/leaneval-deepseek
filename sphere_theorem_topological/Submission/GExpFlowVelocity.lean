import Submission.GExpFlow
import Submission.GExpRayVelocity

/-!
# The state of a `GExp`-ray at the end of a chart-flow box

`Submission.GExpFlow.GExp_eq_chartFlow` identifies the value of `GExp` on a chart-flow box with the
chart-flow itself.  This file adds the **velocity**: at the end of the box (parameter `1` of the ray
`s ↦ GExp q (s • frameVector z₀ q u)`), the velocity of the ray is

`frameVector z₀ (endpoint) (c⁻¹ • (D.α ((φ q), c • u) c⁻¹).2)`

where `c = flowScale D`.  This is the "one-step velocity lemma" of
`Submission/Roadmap.lean` §73.9/§74.6 item 3: it says that the **state** `(position, velocity)` of
the ray at the end of the box is the chart-flow state, which is what a continuation argument along
a long ray (over a finite cover by flow boxes) needs.

The proof re-uses `curveVelocity_GExp_eq_of_isGeodesicAt`: the chart-flow line
`s ↦ (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * s)).1)` is a geodesic with initial data `(q, w)`
(smoothness/geodesy from the chart ODE, non-vanishing velocity from the constancy of the chart
metric along a chart geodesic), so the velocity of the ray agrees with its velocity; the latter is
computed by `curveVelocity_chartCurve`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.ChartBounds
open Submission.ChartConnection
open Submission.GeodesicGlobal
open Submission.RauchGen
open Submission.GExpFlow
open Submission.GExpRayVelocity

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GExpFlowVelocity

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable {z₀ : M} {Z : Set M}

/-- **The velocity of a `GExp`-ray at the end of a chart-flow box.** -/
theorem curveVelocity_GExp_chartFlow (hmet : IsMetricCompatible cov)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {q : M} (hqs : q ∈ (extChartAt I z₀).source) {u : E}
    (hph : ((extChartAt I z₀) q, flowScale D • u) ∈ D.O) (hu : u ≠ 0) :
    curveVelocity (I := I)
        (fun s : ℝ => GExp (cov := cov) hmet q (s • frameVector (I := I) z₀ q u)) 1
      = frameVector (I := I) z₀
          ((extChartAt I z₀).symm
            ((D.α ((extChartAt I z₀) q, flowScale D • u) (flowScale D)⁻¹).1))
          ((flowScale D)⁻¹ • (D.α ((extChartAt I z₀) q, flowScale D • u) (flowScale D)⁻¹).2) := by
  classical
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
  have hpt0 : (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * 0)).1) = q := by
    rw [mul_zero, D.h0 p₀ hp₀O, hp₀def]
    simp only [Prod.fst]
    exact (extChartAt I z₀).left_inv hqs
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
  -- the initial velocity of the chart-flow curve
  have hvr : c⁻¹ • (D.α p₀ (c⁻¹ * 0)).2 = u := by
    rw [mul_zero, D.h0 p₀ hp₀O, hp₀def]
    simp only [Prod.snd]
    rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
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
  -- the one-step velocity lemma
  have hVne : frameVector (I := I) z₀ q u ≠ 0 := by
    rw [hwdef] at hwv
    exact norm_pos_iff.mp hwv
  have hγ0 : (fun s : ℝ => (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * s)).1)) 0 = q := hpt0
  have htransfer : ∀ t ∈ Icc (0 : ℝ) (5 / 4),
      curveVelocity (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet q (s • frameVector (I := I) z₀ q u)) t
        = curveVelocity (I := I)
          (fun s : ℝ => (extChartAt I z₀).symm ((D.α p₀ (c⁻¹ * s)).1)) t :=
    curveVelocity_GExp_eq_of_isGeodesicAt (cov := cov) hmet (p := q)
      (V := frameVector (I := I) z₀ q u) hVne (a := -1) (b := 3 / 2) (T := 5 / 4)
      (by norm_num) (by norm_num) (by norm_num) hγsm hγgeo hγne hγ0 hγvel
  -- the velocity of the chart-flow curve at `1`
  have hvel1 := curveVelocity_chartCurve (I := I) (x₀ := z₀)
    (u := fun s : ℝ => (D.α p₀ (c⁻¹ * s)).1)
    (v := c⁻¹ • (D.α p₀ (c⁻¹ * 1)).2) (t := 1) (hgc.2.2.2.1 1 (by norm_num))
    (hgc.2.2.1 1 (by norm_num))
    (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (by norm_num : (1 : ℝ) ∈ Ioo (-2) 2))
      (fun s hs => hgc.2.2.1 s hs))
  rw [htransfer 1 (by norm_num : (1 : ℝ) ∈ Icc 0 (5 / 4)), hvel1]
  rw [mul_one]

end

end Submission.GExpFlowVelocity
