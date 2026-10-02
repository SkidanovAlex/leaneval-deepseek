import Mathlib
import Submission.Work.ThomBordism.Grassmann.Smooth.Chart.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Smoothness of the change of graph chart

The chart-change map `graphChange S T` (Defs) is a rational expression in the affine variable
`d : Amb k →L[ℝ] Amb m`: it is

`d ↦ (projC T) ∘ graphMap S d ∘ ((projS T) ∘ graphMap S d)⁻¹`,

where `·⁻¹` is `Ring.inverse` on the (finite-dimensional, hence Banach) algebra
`Amb k →L[ℝ] Amb k`.  Since `d ↦ (projS T) ∘ graphMap S d` is affine and `Ring.inverse` is
analytic on the open set of units (`analyticOnNhd_inverse`), the chart change is smooth (indeed
analytic) on the set `{d | graphUnit S T d}` where the inverse exists.

We prove the statement for an arbitrary order `n`, and obtain the requested `C^∞` statement as a
specialization.
-/

namespace Work.ThomBordism.Grassmann.Smooth.Chart

open scoped Topology ContDiff

/-- The change of chart `S → T` on graph data is `C^n` on the open set where the inverse used to
define it exists, for every order `n`. -/
theorem contDiffOn_graphChange_gen {k m : ℕ} (S T : ChartIdx k m) (n : WithTop ENat) :
    ContDiffOn ℝ n (graphChange S T) {d : Amb k →L[ℝ] Amb m | graphUnit S T d} := by
  intro d hd
  have hunit : IsUnit ((projS T).comp (graphMap S d)) := hd
  -- `d ↦ graphMap S d` is affine in `d`
  have hgm : ContDiff ℝ n (fun d : Amb k →L[ℝ] Amb m => graphMap S d) := by
    have h : (fun d : Amb k →L[ℝ] Amb m => graphMap S d)
        = fun d => inclS S +
            (ContinuousLinearMap.compL ℝ (Amb k) (Amb m) (Amb (k + m)) (inclC S)) d := by
      funext d
      rw [ContinuousLinearMap.compL_apply, graphMap]
    rw [h]
    exact contDiff_const.add (ContinuousLinearMap.contDiff _)
  have hgm' : ContDiffWithinAt ℝ n (fun d : Amb k →L[ℝ] Amb m => graphMap S d)
      {d : Amb k →L[ℝ] Amb m | graphUnit S T d} d := hgm.contDiffWithinAt
  -- `d ↦ (projS T) ∘ graphMap S d` is the composition of `graphMap` with a continuous linear map
  have hu : ContDiffWithinAt ℝ n (fun d : Amb k →L[ℝ] Amb m => (projS T).comp (graphMap S d))
      {d : Amb k →L[ℝ] Amb m | graphUnit S T d} d := by
    have h : (fun d : Amb k →L[ℝ] Amb m => (projS T).comp (graphMap S d))
        = (fun f : Amb k →L[ℝ] Amb (k + m) => (projS T).comp f) ∘
            (fun d : Amb k →L[ℝ] Amb m => graphMap S d) := rfl
    rw [h]
    exact (ContinuousLinearMap.contDiff
      ((ContinuousLinearMap.compL ℝ (Amb k) (Amb (k + m)) (Amb k)) (projS T))).comp_contDiffWithinAt hgm'
  -- on the set of units, `Ring.inverse` is `C^n`
  have hinv : ContDiffWithinAt ℝ n
      (fun d : Amb k →L[ℝ] Amb m => Ring.inverse ((projS T).comp (graphMap S d)))
      {d : Amb k →L[ℝ] Amb m | graphUnit S T d} d := by
    have h : ContDiffWithinAt ℝ n
        (Ring.inverse ∘ fun d : Amb k →L[ℝ] Amb m => (projS T).comp (graphMap S d))
        {d : Amb k →L[ℝ] Amb m | graphUnit S T d} d :=
      (contDiffAt_ringInverse (n := n) ℝ hunit.unit).comp_contDiffWithinAt d hu
    exact h
  have hprod : ContDiffWithinAt ℝ n
      (fun d : Amb k →L[ℝ] Amb m =>
        (graphMap S d).comp (Ring.inverse ((projS T).comp (graphMap S d))))
      {d : Amb k →L[ℝ] Amb m | graphUnit S T d} d := hgm'.clm_comp hinv
  -- compose with the (continuous linear) left multiplication by `projC T`
  have hP : ContDiffWithinAt ℝ n
      ((fun f : Amb k →L[ℝ] Amb (k + m) => (projC T).comp f) ∘
        (fun d : Amb k →L[ℝ] Amb m =>
          (graphMap S d).comp (Ring.inverse ((projS T).comp (graphMap S d)))))
      {d : Amb k →L[ℝ] Amb m | graphUnit S T d} d :=
    (ContinuousLinearMap.contDiff
      ((ContinuousLinearMap.compL ℝ (Amb k) (Amb (k + m)) (Amb m)) (projC T))).comp_contDiffWithinAt hprod
  exact hP

/-- **The change of chart `S → T` on graph data is smooth** on the set where the inverse defining
it exists. -/
theorem contDiffOn_graphChange {k m : ℕ} (S T : ChartIdx k m) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (graphChange S T)
      {d : Amb k →L[ℝ] Amb m | graphUnit S T d} :=
  contDiffOn_graphChange_gen S T _

end Work.ThomBordism.Grassmann.Smooth.Chart
