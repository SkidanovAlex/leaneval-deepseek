import Submission.JacobiCoords

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.JacobiCoords

/-!
# Changing the chart of a field along a curve

The chart coordinates `chartCoords z γ V` of a field `V` along a curve `γ` (defined through the
tangential trivialization at `z`) depend on `z`, and the two descriptions are related by the
coordinate change of the two trivializations.  This module makes that explicit (both for the
*values* and for the *regularity*), which is what allows a field defined by coordinates in one chart
to be used in a cover whose pieces carry other charts.

* `chartCoords_eq_coordChangeL` — the pointwise identification with
  `Trivialization.coordChangeL`;
* `contDiffOn_chartCoords_frameVector` — `C^∞` of the chart coordinates of a field given by smooth
  coordinates in another chart;
* **`contDiffOn_chartCoords_of_chartCoords`** — the change-of-chart statement for the coordinates of
  a field along a curve: `C^∞` in one chart on an open set on which `γ` stays in both chart sources
  implies `C^∞` in the other.

This is the missing tool of Roadmap §100.13 (item 2): it lets the perturbation `W` (defined by its
coordinates in the chart of the piece containing the conjugate time) be expressed in the chart of
*any* piece without introducing a chart transition by hand.
-/

namespace Submission.ChartCoordsTrans

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

/-- The chart coordinates of a tangent vector in two charts are related by the coordinate change of
the two tangent trivializations. -/
lemma chartCoords_eq_coordChangeL {z z' : M} {γ : ℝ → M} {a : ℝ → E} {t : ℝ}
    (hz : γ t ∈ (chartAt H z).source) (hz' : γ t ∈ (chartAt H z').source) :
    chartCoords (I := I) z' γ (fun s => frameVector (I := I) z (γ s) (a s)) t
      = Trivialization.coordChangeL ℝ
          (trivializationAt E (TangentSpace I) z)
          (trivializationAt E (TangentSpace I) z') (γ t) (a t) := by
  set e := trivializationAt E (TangentSpace I) z with he
  set e' := trivializationAt E (TangentSpace I) z' with he'
  have hb : γ t ∈ e.baseSet := by rw [he]; simpa [← extChartAt_source] using hz
  have hb' : γ t ∈ e'.baseSet := by rw [he']; simpa [← extChartAt_source] using hz'
  rw [chartCoords]
  show e'.continuousLinearMapAt ℝ (γ t) (frameVector (I := I) z (γ t) (a t)) = _
  rw [frameVector, Trivialization.symmL_apply _ hb,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) (e := e') hb']
  rw [← Trivialization.mk_coordChangeL (R := ℝ) (e := e) (e' := e') ⟨hb, hb'⟩ (a t)]

/-- **Continuity/smoothness of the chart coordinates of a field defined by coordinates in another
chart**: if `γ` stays in both chart sources on the open set `U` and `a` is `C^∞` on `U`, then the
chart-`z'` coordinates of the field `t ↦ frameVector z (γ t) (a t)` are `C^∞` on `U`. -/
theorem contDiffOn_chartCoords_frameVector
    {z z' : M} {γ : ℝ → M} {a : ℝ → E} {U : Set ℝ}
    (hU : IsOpen U) (ha : ContDiffOn ℝ ∞ a U) (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ U)
    (hsrc : ∀ t ∈ U, γ t ∈ (chartAt H z).source)
    (hsrc' : ∀ t ∈ U, γ t ∈ (chartAt H z').source) :
    ContDiffOn ℝ ∞ (fun t => chartCoords (I := I) z' γ
      (fun s => frameVector (I := I) z (γ s) (a s)) t) U := by
  set e := trivializationAt E (TangentSpace I) z with he
  set e' := trivializationAt E (TangentSpace I) z' with he'
  have hbase : ∀ t ∈ U, γ t ∈ e.baseSet ∩ e'.baseSet := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [he]; simpa [← extChartAt_source] using hsrc t ht
    · rw [he']; simpa [← extChartAt_source] using hsrc' t ht
  have hcc : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun q : M => (e.coordChangeL ℝ e' q : E →L[ℝ] E)) (e.baseSet ∩ e'.baseSet) :=
    contMDiffOn_coordChangeL (𝕜 := ℝ) e e'
  have hcl : ContDiffOn ℝ ∞ (fun t : ℝ => (e.coordChangeL ℝ e' (γ t) : E →L[ℝ] E)) U := by
    have h1 : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E →L[ℝ] E) ∞
        (fun t : ℝ => (e.coordChangeL ℝ e' (γ t) : E →L[ℝ] E)) U :=
      hcc.comp hγ (fun t ht => hbase t ht)
    exact contMDiffOn_iff_contDiffOn.mp h1
  have h2 : ContDiffOn ℝ ∞
      (fun t : ℝ => (e.coordChangeL ℝ e' (γ t) : E →L[ℝ] E) (a t)) U :=
    hcl.clm_apply ha
  refine h2.congr fun t ht => ?_
  exact (chartCoords_eq_coordChangeL (I := I) (hsrc t ht) (hsrc' t ht))

/-- **Change of chart for the coordinates of a field along a curve.**  If the chart-`z` coordinates of
a field `V` along `γ` are `C^∞` on an open set `U` on which `γ` stays in both chart sources, then so
are the chart-`z'` coordinates. -/
theorem contDiffOn_chartCoords_of_chartCoords
    {z z' : M} {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ U)
    (hsrc : ∀ t ∈ U, γ t ∈ (chartAt H z).source)
    (hsrc' : ∀ t ∈ U, γ t ∈ (chartAt H z').source)
    (hV : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ V) U) :
    ContDiffOn ℝ ∞ (chartCoords (I := I) z' γ V) U := by
  refine (contDiffOn_chartCoords_frameVector (I := I) hU hV hγ hsrc hsrc').congr ?_
  intro t ht
  simp only [chartCoords]
  rw [Submission.GlobalBM.frameVector_continuousLinearMapAt (I := I) z (γ t) (hsrc t ht) (V t)]

end

end Submission.ChartCoordsTrans
