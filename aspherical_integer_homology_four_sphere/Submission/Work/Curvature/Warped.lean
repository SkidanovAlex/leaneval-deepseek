import Submission.Work.Curvature.Deriv
import Submission.Work.Curvature.warpedMetric_chrWarped_koszul
import Submission.Work.Curvature.warpedMetric_dBmodel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The warped model: identification and curvature

This file assembles the warped chain of the curvature chapter:

* `koszulChr_warpedMetric` — the Christoffel symbol of `warpedMetric f h` is `chrWarped`;
* `dBmodel_warpedMetric` — its derivative;
* `modelCurv_warpedMetric` — the explicit model curvature;
* `warped_sec_eq` / `warped_sec_nonpos` — the sectional curvature formula and its sign.
-/

open scoped RealInnerProductSpace
open Filter Topology
open Classical

namespace Work.Curvature

noncomputable section

/-- **The Christoffel symbol of the warped metric.** -/
theorem koszulChr_warpedMetric (f h : ℝ → ℝ) (q : E4) (a b : E4)
    (hf : f (q 0) ≠ 0) (hh : h (q 0) ≠ 0)
    (hfd : DifferentiableAt ℝ f (q 0)) (hhd : DifferentiableAt ℝ h (q 0)) :
    koszulChr (warpedMetric f h) q a b = chrWarped f h q a b :=
  koszulChr_eq_of_forall (fun x y c => warpedMetric_sub_fst f h q x y c)
    (warpedMetric_pos' f h q hf hh)
    (fun c => warpedMetric_chrWarped_koszul f h q a b c hfd hhd hf hh)

/-- `chrWarped` is linear in its first argument. -/
theorem chrWarped_smul_fst (f h : ℝ → ℝ) (q : E4) (c : ℝ) (x b : E4) :
    chrWarped f h q (c • x) b = c • chrWarped f h q x b := by
  refine PiLp.ext fun i => ?_
  fin_cases i <;>
    simp [chrWarped, PiLp.smul_apply] <;>
    ring

/-- **Derivative of the warped Christoffel symbol**, unconditional form. -/
theorem dBmodel_warpedMetric (f h : ℝ → ℝ) (q : E4) (d a b : E4)
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h) (hf0 : f (q 0) ≠ 0) (hh0 : h (q 0) ≠ 0) :
    dBmodel (warpedMetric f h) q d a b = (d 0) • chrWarpedDeriv f h (q 0) a b := by
  refine warpedMetric_dBmodel f h q d a b hf hh hf0 hh0 ?_
  have hcont_f : Continuous fun q' : E4 => f (q' 0) := hf.continuous.comp (coord 0).continuous
  have hcont_h : Continuous fun q' : E4 => h (q' 0) := hh.continuous.comp (coord 0).continuous
  filter_upwards [(isOpen_ne.preimage hcont_f).mem_nhds hf0,
    (isOpen_ne.preimage hcont_h).mem_nhds hh0] with q' hf' hh'
  exact koszulChr_warpedMetric f h q' a b hf' hh'
    ((hf.differentiable (by norm_num)).differentiableAt)
    ((hh.differentiable (by norm_num)).differentiableAt)

/-- **The explicit model curvature of the warped metric.** -/
theorem modelCurv_warpedMetric (f h : ℝ → ℝ) (q : E4) (u v w : E4)
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h) (hf0 : f (q 0) ≠ 0) (hh0 : h (q 0) ≠ 0) :
    modelCurv (warpedMetric f h) q u v w
      = (u 0) • chrWarpedDeriv f h (q 0) w v - (v 0) • chrWarpedDeriv f h (q 0) w u
        + chrWarped f h q (chrWarped f h q w v) u
        - chrWarped f h q (chrWarped f h q w u) v := by
  rw [modelCurv, dBmodel_warpedMetric f h q u w v hf hh hf0 hh0,
    dBmodel_warpedMetric f h q v w u hf hh hf0 hh0]
  simp only [koszulChr_warpedMetric f h q _ _ hf0 hh0
    ((hf.differentiable (by norm_num)).differentiableAt)
    ((hh.differentiable (by norm_num)).differentiableAt)]

end

end Work.Curvature
