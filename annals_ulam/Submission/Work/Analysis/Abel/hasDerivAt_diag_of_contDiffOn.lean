import Mathlib

namespace Work.Analysis.Abel

open MeasureTheory Set Filter
open scoped Topology Interval

/-- **Chain rule along a diagonal for a jointly `C¹` function.**
If `(x,σ) ↦ B x σ` is jointly `C¹` on an open set `U` and `(x, x+y) ∈ U`, then
`u ↦ B u (u+y)` has derivative
`deriv (fun u' => B u' (x+y)) x + deriv (fun v => B x v) (x+y)` at `x`. -/
theorem hasDerivAt_diag_of_contDiffOn {B : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hB : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => B p.1 p.2) U)
    {x y : ℝ} (hxy : (x, x + y) ∈ U) :
    HasDerivAt (fun u : ℝ => B u (u + y))
      (deriv (fun u' : ℝ => B u' (x + y)) x + deriv (fun v : ℝ => B x v) (x + y)) x := by
  have hdp : DifferentiableAt ℝ (fun q : ℝ × ℝ => B q.1 q.2) (x, x + y) :=
    (hB.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hxy)
  have hF : HasFDerivAt (fun q : ℝ × ℝ => B q.1 q.2)
      (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) (x, x + y)) (x, x + y) := hdp.hasFDerivAt
  -- slice in the first variable
  have hg1 : HasFDerivAt (fun e : ℝ => (e, x + y)) (ContinuousLinearMap.inl ℝ ℝ ℝ) x :=
    hasFDerivAt_prodMk_left x (x + y)
  have hcomp1 := hF.comp x hg1
  have hfr1 : fderiv ℝ (fun u' : ℝ => B u' (x + y)) x
      = (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) (x, x + y)).comp
          (ContinuousLinearMap.inl ℝ ℝ ℝ) := hcomp1.fderiv
  have hd1 : deriv (fun u' : ℝ => B u' (x + y)) x
      = (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) (x, x + y)) (1, 0) := by
    calc deriv (fun u' : ℝ => B u' (x + y)) x
        = (fderiv ℝ (fun u' : ℝ => B u' (x + y)) x) 1 := (fderiv_apply_one_eq_deriv).symm
      _ = ((fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) (x, x + y)).comp
              (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1 := by rw [hfr1]
      _ = (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) (x, x + y)) (1, 0) := by
            simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  -- slice in the second variable
  have hg2 : HasFDerivAt (fun e : ℝ => (x, e)) (ContinuousLinearMap.inr ℝ ℝ ℝ) (x + y) :=
    hasFDerivAt_prodMk_right x (x + y)
  have hcomp2 := hF.comp (x + y) hg2
  have hfr2 : fderiv ℝ (fun v : ℝ => B x v) (x + y)
      = (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) (x, x + y)).comp
          (ContinuousLinearMap.inr ℝ ℝ ℝ) := hcomp2.fderiv
  have hd2 : deriv (fun v : ℝ => B x v) (x + y)
      = (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) (x, x + y)) (0, 1) := by
    calc deriv (fun v : ℝ => B x v) (x + y)
        = (fderiv ℝ (fun v : ℝ => B x v) (x + y)) 1 := (fderiv_apply_one_eq_deriv).symm
      _ = ((fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) (x, x + y)).comp
              (ContinuousLinearMap.inr ℝ ℝ ℝ)) 1 := by rw [hfr2]
      _ = (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) (x, x + y)) (0, 1) := by
            simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  -- the diagonal curve `u ↦ (u, u + y)`
  have hid : HasFDerivAt (fun u : ℝ => u + y) (ContinuousLinearMap.id ℝ ℝ) x :=
    (hasFDerivAt_id x).add_const y
  have hc : HasFDerivAt (fun u : ℝ => (u, u + y))
      ((ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ)) x :=
    (hasFDerivAt_id x).prodMk hid
  have hcomp3 := hF.comp x hc
  have hder : HasDerivAt ((fun q : ℝ × ℝ => B q.1 q.2) ∘ (fun u : ℝ => (u, u + y)))
      (((fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) (x, x + y)).comp
        ((ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ))) 1) x :=
    hcomp3.hasDerivAt
  have hval : (((fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) (x, x + y)).comp
        ((ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ))) 1)
      = deriv (fun u' : ℝ => B u' (x + y)) x + deriv (fun v : ℝ => B x v) (x + y) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    simp only [ContinuousLinearMap.id_apply]
    have hp : ((1 : ℝ), (1 : ℝ)) = ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by simp
    rw [hp, map_add, ← hd1, ← hd2]
  rw [hval] at hder
  exact hder

end Work.Analysis.Abel
