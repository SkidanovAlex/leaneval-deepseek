import Mathlib
import Submission.Work.OddBound.PiExtChart
import Submission.Work.OddBound.sqDistChart.sqDist_contDiffAt_charts
import Submission.Work.OddBound.polygon.isCritical_gonEnergy_geodesic
import Submission.Work.OddBound.chartAlgebra.contDiffAt_gonEnergy_piExtChart
import Submission.Work.OddBound.LiftKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the polygon energy in the product extended chart, at an arbitrary point

This is the generalisation of `contDiffAt_gonEnergy_piExtChart` to an arbitrary point `w` of the
source of the product extended chart `piExtChart x`, rather than the chart centre `x` itself.

The proof is by change of chart: the chart `piExtChart w` (centred at `w`) is `C^∞`-compatible with
`piExtChart x` near the point `(piExtChart x) w`, and

`u ↦ gonEnergy p ((piExtChart x).symm u)`

agrees near `(piExtChart x) w` with `v ↦ gonEnergy p ((piExtChart w).symm v)` precomposed with the
transition map `τ u = (piExtChart w) ((piExtChart x).symm u)`.  The latter is `C²` at
`(piExtChart w) w` by `contDiffAt_gonEnergy_piExtChart` (applied with the polygon `w`), `τ` is
`C^∞` (componentwise, since a chart transition of a `C^∞` manifold is `C^∞`), so the composite is
`C²` at `(piExtChart x) w`.
-/

set_option maxHeartbeats 1000000

namespace Work.OddBound.chartAlgebra

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

theorem contDiffAt_gonEnergy_piExtChart_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {N : ℕ} (hN : 3 ≤ N) {p : M} {x w : Fin (N - 1) → M}
    (hwsrc : w ∈ (Work.OddBound.piExtChart (I := I) x).source)
    {R : ℝ} (hR : 0 < R)
    (hinj : ∀ z : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet z R)
    (hsmall : ∀ i : Fin N, Work.OddBound.gonSideLen (I := I) p w i < R) :
    ContDiffAt ℝ 2
      (fun u : (Fin (N - 1)) → E =>
        Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u))
      ((Work.OddBound.piExtChart (I := I) x) w) := by
  -- The inverse of the extended chart `extChartHomeo z` (out of which `piExtChart` is built) is
  -- the same function as the inverse of `extChartAt I z`.
  have hsymm_bridge : ∀ z : M,
      ⇑(Work.OddBound.extChartHomeo (I := I) z).symm = ⇑(extChartAt I z).symm := by
    intro z
    funext y
    rw [extChartAt_coe_symm]
    rfl
  -- The components of the product extended chart at an arbitrary point.
  have hpi : ∀ (v : Fin (N-1) → M) (j : Fin (N-1)),
      (Work.OddBound.piExtChart (I := I) x) v j = (extChartAt I (x j)) (v j) := by
    intro v j
    unfold Work.OddBound.piExtChart
    rw [OpenPartialHomeomorph.pi_apply, Work.OddBound.extChartHomeo_coe, extChartAt_coe]
    rfl
  -- Componentwise source membership of the point `w`.
  have hwj : ∀ j : Fin (N-1), w j ∈ (extChartAt I (x j)).source := by
    intro j
    have h2 : w j ∈ (Work.OddBound.extChartHomeo (I := I) (x j)).source := by
      have h := hwsrc
      unfold Work.OddBound.piExtChart at h
      rw [show (OpenPartialHomeomorph.pi fun i => Work.OddBound.extChartHomeo (I := I) (x i)).source
          = Set.univ.pi (fun i => (Work.OddBound.extChartHomeo (I := I) (x i)).source) from
        PartialEquiv.pi_source _] at h
      exact (Set.mem_univ_pi.mp h) j
    simpa [Work.OddBound.extChartHomeo_source] using h2
  -- Smoothness of a chart transition: if `a` is in the source of the chart at `c`, then
  -- `z ↦ (extChartAt I a) ((extChartAt I c).symm z)` is `C^∞` at the coordinates of `a`.
  have htrans_smooth : ∀ {a c : M}, a ∈ (extChartAt I c).source →
      ContDiffAt ℝ ∞ (fun z : E => (extChartAt I a) ((extChartAt I c).symm z)) ((extChartAt I c) a) := by
    intro a c hac
    have hs₀ : (extChartAt I c) a ∈ (extChartAt I c).target := (extChartAt I c).map_source hac
    have htgt : (extChartAt I c).target ∈ 𝓝 ((extChartAt I c) a) :=
      (OpenPartialHomeomorph.isOpen_extend_target (chartAt H c) (I := I)).mem_nhds hs₀
    have hsmd : ContMDiffAt 𝓘(ℝ,E) I ∞ (extChartAt I c).symm ((extChartAt I c) a) :=
      (contMDiffOn_extChartAt_symm (I := I) (n := ∞) c).contMDiffAt htgt
    have hamd : ContMDiffAt I 𝓘(ℝ,E) ∞ (extChartAt I a) ((extChartAt I c).symm ((extChartAt I c) a)) := by
      rw [(extChartAt I c).left_inv hac]
      exact (contMDiffOn_extChartAt (I := I) (x := a) (n := ∞)).contMDiffAt
        ((chartAt H a).open_source.mem_nhds (mem_chart_source H a))
    exact contMDiffAt_iff_contDiffAt.mp (hamd.comp ((extChartAt I c) a) hsmd)
  -- The transition map from the chart at `x` to the chart at `w`.
  set τ : ((Fin (N-1)) → E) → ((Fin (N-1)) → E) :=
    fun u => (Work.OddBound.piExtChart (I := I) w) ((Work.OddBound.piExtChart (I := I) x).symm u)
    with hτdef
  have hτval : ∀ (u : (Fin (N-1)) → E) (j : Fin (N-1)),
      τ u j = (extChartAt I (w j)) ((extChartAt I (x j)).symm (u j)) := by
    intro u j
    rw [hτdef]
    dsimp only
    unfold Work.OddBound.piExtChart
    rw [OpenPartialHomeomorph.pi_apply, OpenPartialHomeomorph.pi_symm_apply,
      Work.OddBound.extChartHomeo_coe, extChartAt_coe]
    rw [congrFun (hsymm_bridge (x j)) (u j), Function.comp_apply]
  have hτsmooth : ContDiffAt ℝ ∞ τ ((Work.OddBound.piExtChart (I := I) x) w) := by
    rw [contDiffAt_pi]
    intro j
    have hfun : (fun u : (Fin (N-1)) → E => τ u j)
        = fun u => (extChartAt I (w j)) ((extChartAt I (x j)).symm (u j)) := by
      funext u; exact hτval u j
    rw [hfun]
    have hpoint : ((Work.OddBound.piExtChart (I := I) x) w) j = (extChartAt I (x j)) (w j) := hpi w j
    have htrans := htrans_smooth (hwj j)
    rw [← hpoint] at htrans
    have hproj : ContDiffAt ℝ ∞ (fun u : (Fin (N-1)) → E => u j)
        ((Work.OddBound.piExtChart (I := I) x) w) :=
      (((ContinuousLinearMap.proj (R := ℝ) j : ((Fin (N-1)) → E) →L[ℝ] E)).contDiff).contDiffAt
    simpa only [Function.comp_def] using htrans.comp ((Work.OddBound.piExtChart (I := I) x) w) hproj
  -- Continuity of the product chart inverse at `(piExtChart x) w`.
  have hcont_symm : ContinuousAt (fun u : (Fin (N-1)) → E =>
      (Work.OddBound.piExtChart (I := I) x).symm u) ((Work.OddBound.piExtChart (I := I) x) w) := by
    rw [continuousAt_pi]
    intro j
    have hfun : (fun y : (Fin (N-1)) → E => (Work.OddBound.piExtChart (I := I) x).symm y j)
        = fun y => (extChartAt I (x j)).symm (y j) := by
      funext y; exact piExtChart_symm_apply (I := I) x y j
    rw [hfun]
    have htgtj : (extChartAt I (x j)).target ∈ 𝓝 (((Work.OddBound.piExtChart (I := I) x) w) j) := by
      rw [hpi w j]
      have := (extChartAt I (x j)).map_source (hwj j)
      exact (OpenPartialHomeomorph.isOpen_extend_target (chartAt H (x j)) (I := I)).mem_nhds this
    have hmd : ContMDiffAt 𝓘(ℝ,E) I ∞ (extChartAt I (x j)).symm
        (((Work.OddBound.piExtChart (I := I) x) w) j) :=
      (contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x j)).contMDiffAt htgtj
    have hcast : ContinuousAt (fun z : E => (extChartAt I (x j)).symm z)
        (((Work.OddBound.piExtChart (I := I) x) w) j) := hmd.continuousAt
    have hprojc : ContinuousAt (fun u : (Fin (N-1)) → E => u j)
        ((Work.OddBound.piExtChart (I := I) x) w) :=
      (((ContinuousLinearMap.proj (R := ℝ) j : ((Fin (N-1)) → E) →L[ℝ] E)).continuous).continuousAt
    simpa only [Function.comp_def] using hcast.comp (f := fun u : (Fin (N-1)) → E => u j)
      (x := ((Work.OddBound.piExtChart (I := I) x) w)) hprojc
  have hτu₀ : τ ((Work.OddBound.piExtChart (I := I) x) w) = (Work.OddBound.piExtChart (I := I) w) w := by
    rw [hτdef]
    simp only
    rw [(Work.OddBound.piExtChart (I := I) x).left_inv hwsrc]
  -- The polygon energy in the chart at `w` is `C²` at the coordinates of `w`.
  have hH := contDiffAt_gonEnergy_piExtChart (I := I) (cov := cov)
    hmet htor hN (p := p) (x := w) hR hinj hsmall
  have hcomp : ContDiffAt ℝ 2 (fun u : (Fin (N-1)) → E =>
      Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) w).symm (τ u)))
      ((Work.OddBound.piExtChart (I := I) x) w) := by
    have h2 : ContDiffAt ℝ 2 (fun v => Work.OddBound.gonEnergy (I := I) p
        ((Work.OddBound.piExtChart (I := I) w).symm v)) (τ ((Work.OddBound.piExtChart (I := I) x) w)) := by
      rw [hτu₀]; exact hH
    exact h2.comp _ (hτsmooth.of_le (by decide))
  -- Near `(piExtChart x) w` the two expressions agree.
  refine hcomp.congr_of_eventuallyEq ?_
  have hsrc : (Work.OddBound.piExtChart (I := I) w).source ∈ 𝓝
      ((Work.OddBound.piExtChart (I := I) x).symm ((Work.OddBound.piExtChart (I := I) x) w)) := by
    rw [(Work.OddBound.piExtChart (I := I) x).left_inv hwsrc]
    exact (Work.OddBound.piExtChart (I := I) w).open_source.mem_nhds
      (Work.OddBound.mem_piExtChart_source (I := I) w)
  have hpre : ∀ᶠ u in 𝓝 ((Work.OddBound.piExtChart (I := I) x) w),
      (Work.OddBound.piExtChart (I := I) x).symm u ∈ (Work.OddBound.piExtChart (I := I) w).source :=
    hcont_symm.preimage_mem_nhds hsrc
  filter_upwards [hpre] with u hu
  show Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u)
      = Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) w).symm (τ u))
  rw [hτdef]
  simp only
  rw [(Work.OddBound.piExtChart (I := I) w).left_inv hu]

end Work.OddBound.chartAlgebra
