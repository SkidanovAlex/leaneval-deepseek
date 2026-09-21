import Mathlib

namespace Work.Analysis.Abel

open MeasureTheory Set Filter
open scoped Topology Interval

/-- **Continuity of the first partial derivative of a jointly `C¹` function on an open set.**
If `(x,σ) ↦ B x σ` is jointly `C¹` on an open set `U ⊆ ℝ × ℝ`, then
`(x,σ) ↦ deriv (fun x' => B x' σ) x` is continuous on `U`. -/
theorem continuousOn_deriv_slice_fst {B : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hB : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => B p.1 p.2) U) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun x : ℝ => B x p.2) p.1) U := by
  -- The map `(x,σ) ↦ fderiv B (x,σ) (1,0)` is continuous on `U`: `fderiv B` is continuous by
  -- `C¹`-ness on an open set, and evaluation at a fixed vector is continuous.
  have hcont :
      ContinuousOn (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) p) (1, 0)) U :=
    (hB.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  -- It remains to identify `deriv (fun x => B x σ) x` with `fderiv B (x,σ) (1,0)` on `U`.
  refine hcont.congr (fun p hp => ?_)
  have hdp : DifferentiableAt ℝ (fun q : ℝ × ℝ => B q.1 q.2) p :=
    (hB.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp)
  have hF : HasFDerivAt (fun q : ℝ × ℝ => B q.1 q.2)
      (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) p) p := hdp.hasFDerivAt
  -- The slice `x ↦ B x p.2` is the composition of `q ↦ B q.1 q.2` with `x ↦ (x, p.2)`,
  -- whose derivative at `p.1` is the inclusion `ℝ →L[ℝ] ℝ × ℝ`.
  have hg : HasFDerivAt (fun x : ℝ => (x, p.2)) (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 :=
    hasFDerivAt_prodMk_left p.1 p.2
  have hcomp := hF.comp p.1 hg
  have hcomp' : fderiv ℝ (fun x : ℝ => B x p.2) p.1
      = (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) p).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) :=
    hcomp.fderiv
  calc deriv (fun x : ℝ => B x p.2) p.1
      = (fderiv ℝ (fun x : ℝ => B x p.2) p.1) 1 := (fderiv_apply_one_eq_deriv).symm
    _ = ((fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) p).comp
            (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1 := by rw [hcomp']
    _ = (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) p) (1, 0) := by
          simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

end Work.Analysis.Abel
