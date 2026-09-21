import Mathlib

namespace Work.Analysis.Abel

open MeasureTheory Set Filter
open scoped Topology Interval

/-- **Continuity of the second partial derivative of a jointly `C¹` function on an open set.**
If `(x,σ) ↦ B x σ` is jointly `C¹` on an open set `U ⊆ ℝ × ℝ`, then
`(x,σ) ↦ deriv (fun σ' => B x σ') σ` is continuous on `U`. -/
theorem continuousOn_deriv_slice_snd {B : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hB : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => B p.1 p.2) U) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun v : ℝ => B p.1 v) p.2) U := by
  -- The map `(x,σ) ↦ fderiv B (x,σ) (0,1)` is continuous on `U`: `fderiv B` is continuous by
  -- `C¹`-ness on an open set, and evaluation at a fixed vector is continuous.
  have hcont :
      ContinuousOn (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) p) (0, 1)) U :=
    (hB.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  -- It remains to identify `deriv (fun v => B p.1 v) σ` with `fderiv B (p.1,σ) (0,1)` on `U`.
  refine hcont.congr (fun p hp => ?_)
  have hdp : DifferentiableAt ℝ (fun q : ℝ × ℝ => B q.1 q.2) p :=
    (hB.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp)
  have hF : HasFDerivAt (fun q : ℝ × ℝ => B q.1 q.2)
      (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) p) p := hdp.hasFDerivAt
  -- The slice `v ↦ B p.1 v` is the composition of `q ↦ B q.1 q.2` with `v ↦ (p.1, v)`,
  -- whose derivative at `p.2` is the inclusion `ℝ →L[ℝ] ℝ × ℝ` into the second factor.
  have hg : HasFDerivAt (fun v : ℝ => (p.1, v)) (ContinuousLinearMap.inr ℝ ℝ ℝ) p.2 :=
    hasFDerivAt_prodMk_right p.1 p.2
  have hcomp := hF.comp p.2 hg
  have hcomp' : fderiv ℝ (fun v : ℝ => B p.1 v) p.2
      = (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) p).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) :=
    hcomp.fderiv
  calc deriv (fun v : ℝ => B p.1 v) p.2
      = (fderiv ℝ (fun v : ℝ => B p.1 v) p.2) 1 := (fderiv_apply_one_eq_deriv).symm
    _ = ((fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) p).comp
            (ContinuousLinearMap.inr ℝ ℝ ℝ)) 1 := by rw [hcomp']
    _ = (fderiv ℝ (fun q : ℝ × ℝ => B q.1 q.2) p) (0, 1) := by
          simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

end Work.Analysis.Abel
