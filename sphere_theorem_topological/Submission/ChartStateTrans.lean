import Submission.ChartCoordsTrans

/-!
# The state transition between two charts

This module contains the two chart bookkeeping lemmas needed by the **chunked chart-flow** proof of
the joint continuity of `(q, v) ↦ GExp q v` in the base point (Roadmap §128.3):

* `contMDiffOn_coordChange_state` — the change of chart for the **coordinates of a tangent vector**,
  jointly in the point and in the coordinates;
* `contMDiffOn_stateTransition` — the transition map between two charts on the pair
  (coordinates of a point, coordinates of a tangent vector there): from the chart-`z` coordinates to
  the chart-`z'` coordinates, jointly `C^∞`.

The consistency lemmas `stateTransition_symm_fst` and `stateTransition_frameVector` say that the
transition map describes *the same* intrinsic point and *the same* intrinsic tangent vector.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartBounds
open Submission.ChartConnection
open Submission.GExpFlow
open Submission.JacobiCoords

namespace Submission.ChartStateTrans

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]
  {z z' : M}

/-- **The chart change of the coordinates of a tangent vector**, jointly in the point and in the
coordinates: if `U` is a set of points lying in both chart sources, then
`(q, w) ↦ (coordChangeL z z' q) w` is `C^∞` on `U ×ˢ univ`. -/
theorem contMDiffOn_coordChange_state {U : Set M}
    (hU : U ⊆ (chartAt H z).source ∩ (chartAt H z').source) :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun qw : M × E => (Trivialization.coordChangeL ℝ
        (trivializationAt E (TangentSpace I) z)
        (trivializationAt E (TangentSpace I) z') qw.1) qw.2) (U ×ˢ (univ : Set E)) := by
  set e := trivializationAt E (TangentSpace I) z with he
  set e' := trivializationAt E (TangentSpace I) z' with he'
  have hbase : U ⊆ e.baseSet ∩ e'.baseSet := by
    intro q hq
    refine ⟨?_, ?_⟩
    · rw [he]; simpa [← extChartAt_source] using (hU hq).1
    · rw [he']; simpa [← extChartAt_source] using (hU hq).2
  have hcc : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun q : M => (e.coordChangeL ℝ e' q : E →L[ℝ] E)) (e.baseSet ∩ e'.baseSet) :=
    contMDiffOn_coordChangeL (𝕜 := ℝ) e e'
  have h1 : ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun qw : M × E => (e.coordChangeL ℝ e' qw.1 : E →L[ℝ] E)) (U ×ˢ (univ : Set E)) :=
    hcc.comp contMDiffOn_fst (fun qw hqw => hbase hqw.1)
  exact h1.clm_apply contMDiffOn_snd

/-- **The state transition between two charts.**  From the chart-`z` coordinates `(x, w)` of a point
of `M` and of a tangent vector there, produce the chart-`z'` coordinates of the point and of the
vector.  The map is `C^∞` on the set of `(x, w)` for which the point lies in both chart sources. -/
theorem contMDiffOn_stateTransition :
    ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun xw : E × E =>
        ((extChartAt I z') ((extChartAt I z).symm xw.1),
         (Trivialization.coordChangeL ℝ
            (trivializationAt E (TangentSpace I) z)
            (trivializationAt E (TangentSpace I) z') ((extChartAt I z).symm xw.1)) xw.2))
      (((extChartAt I z).target ∩ ((extChartAt I z).symm ⁻¹' (chartAt H z').source)) ×ˢ
        (univ : Set E)) := by
  set U : Set M := (extChartAt I z).symm '' ((extChartAt I z).target ∩
    ((extChartAt I z).symm ⁻¹' (chartAt H z').source)) with hUdef
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (fun x : E => (extChartAt I z).symm x)
      ((extChartAt I z).target ∩ ((extChartAt I z).symm ⁻¹' (chartAt H z').source)) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) z).mono (Set.inter_subset_left)
  have hUsub : U ⊆ (chartAt H z).source ∩ (chartAt H z').source := by
    rintro q ⟨x, ⟨hxt, hxs⟩, rfl⟩
    exact ⟨by simpa using (extChartAt I z).map_target hxt, by simpa using hxs⟩
  have h1 : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, E)) I ∞
      (fun xw : E × E => (extChartAt I z).symm xw.1)
      (((extChartAt I z).target ∩ ((extChartAt I z).symm ⁻¹' (chartAt H z').source)) ×ˢ
        (univ : Set E)) :=
    hsymm.comp contMDiffOn_fst (fun xw hxw => hxw.1)
  have h2 : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun xw : E × E => (extChartAt I z') ((extChartAt I z).symm xw.1))
      (((extChartAt I z).target ∩ ((extChartAt I z).symm ⁻¹' (chartAt H z').source)) ×ˢ
        (univ : Set E)) :=
    (contMDiffOn_extChartAt (I := I) (x := z') (n := ∞)).comp h1
      (fun xw hxw => by
        have : (extChartAt I z).symm xw.1 ∈ (chartAt H z').source := hxw.1.2
        simpa using this)
  have hpair : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E)) ∞
      (fun xw : E × E => ((extChartAt I z).symm xw.1, xw.2))
      (((extChartAt I z).target ∩ ((extChartAt I z).symm ⁻¹' (chartAt H z').source)) ×ˢ
        (univ : Set E)) := by
    refine (h1.prodMk contMDiffOn_snd).mono ?_
    intro xw hxw
    exact hxw
  have h3 : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun xw : E × E =>
        (Trivialization.coordChangeL ℝ
          (trivializationAt E (TangentSpace I) z)
          (trivializationAt E (TangentSpace I) z') ((extChartAt I z).symm xw.1)) xw.2)
      (((extChartAt I z).target ∩ ((extChartAt I z).symm ⁻¹' (chartAt H z').source)) ×ˢ
        (univ : Set E)) :=
    (contMDiffOn_coordChange_state (I := I) hUsub).comp hpair
      (fun xw hxw => ⟨⟨xw.1, hxw.1, rfl⟩, hxw.2⟩)
  exact (h2.prodMk h3).mono (by
    intro xw hxw; exact hxw)

/-! ## Consistency of the transition with the intrinsic data -/

/-- The transition does not move the point: the chart-`z'` position of the point is the chart-`z` one,
read through the two charts. -/
lemma stateTransition_symm_fst {x : E} (hx : x ∈ (extChartAt I z).target)
    (hx' : (extChartAt I z).symm x ∈ (chartAt H z').source) :
    (extChartAt I z').symm ((extChartAt I z') ((extChartAt I z).symm x))
      = (extChartAt I z).symm x :=
  (extChartAt I z').left_inv (by simpa using hx')

/-- The transition does not move the tangent vector: reading the coordinates `w` of a vector in the
chart `z`, changing to the chart `z'`, and forming the frame vector there gives back the original
vector. -/
lemma stateTransition_frameVector {x : E} (hx : x ∈ (extChartAt I z).target)
    (hxz : (extChartAt I z).symm x ∈ (chartAt H z).source)
    (hx' : (extChartAt I z).symm x ∈ (chartAt H z').source) (w : E) :
    frameVector (I := I) z' ((extChartAt I z).symm x)
        ((Trivialization.coordChangeL ℝ
          (trivializationAt E (TangentSpace I) z)
          (trivializationAt E (TangentSpace I) z') ((extChartAt I z).symm x)) w)
      = frameVector (I := I) z ((extChartAt I z).symm x) w := by
  set p : M := (extChartAt I z).symm x with hp
  have hps : p ∈ (extChartAt I z).source := by
    rw [hp]; simpa using (extChartAt I z).map_target hx
  have hps' : p ∈ (extChartAt I z').source := by simpa using hx'
  have hcoord : (Trivialization.coordChangeL ℝ
        (trivializationAt E (TangentSpace I) z)
        (trivializationAt E (TangentSpace I) z') p) w
      = (trivializationAt E (TangentSpace I) z').continuousLinearMapAt ℝ p
          (frameVector (I := I) z p w) := by
    have h := Submission.ChartCoordsTrans.chartCoords_eq_coordChangeL (I := I)
      (z := z) (z' := z') (γ := fun _ : ℝ => p) (a := fun _ : ℝ => w) (t := 0)
      (by simpa using hps) (by simpa using hps')
    simpa [chartCoords, hp] using h.symm
  rw [hcoord]
  exact frameVector_clm (I := I) (by simpa using hps') (frameVector (I := I) z p w)

end

end Submission.ChartStateTrans
