import Submission.Work.Curvature.Deriv
import Submission.Work.Curvature.uhsMetric_chrUHS_koszul
import Submission.Work.Curvature.uhsMetric_dBmodel
import Submission.Work.Curvature.uhs_sec

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The upper half space model: identification and curvature

This file assembles the UHS chain of the curvature chapter:

* `chrUHSvec_smul_fst` — `chrUHSvec` is linear in its first argument;
* `koszulChr_uhsMetric` — the Christoffel symbol of `uhsMetric` is `chrUHS`;
* `dBmodel_uhsMetric` — its derivative;
* `modelCurv_uhsMetric` — the explicit model curvature;
* `uhs_sec` — the sectional curvature is constant `−1`.
-/

open scoped RealInnerProductSpace
open Filter Topology
open Classical

namespace Work.Curvature

noncomputable section

/-- `chrUHSvec` is linear in its first argument. -/
theorem chrUHSvec_smul_fst (c : ℝ) (x b : E4) :
    chrUHSvec (c • x) b = c • chrUHSvec x b := by
  refine PiLp.ext fun i => ?_
  fin_cases i <;>
    simp [chrUHSvec, PiLp.smul_apply] <;>
    ring

/-- **The Christoffel symbol of the UHS metric.** -/
theorem koszulChr_uhsMetric (q : E4) (hq : 0 < q 3) (a b : E4) :
    koszulChr uhsMetric q a b = chrUHS q a b :=
  koszulChr_eq_of_forall (fun x y c => uhsMetric_sub_fst q x y c)
    (uhsMetric_pos q (ne_of_gt hq))
    (fun c => uhsMetric_chrUHS_koszul q (ne_of_gt hq) a b c)

/-- The Gram determinant of the UHS metric is nonnegative (Cauchy–Schwarz). -/
theorem uhsMetric_gram_nonneg (q u v : E4) :
    0 ≤ uhsMetric q u u * uhsMetric q v v - uhsMetric q u v ^ 2 := by
  have hs : (0 : ℝ) ≤ ((q 3)⁻¹ ^ 2) ^ 2 := sq_nonneg _
  have h := real_inner_mul_inner_self_le u v
  rw [uhsMetric_apply, uhsMetric_apply, uhsMetric_apply]
  nlinarith [h, hs]

/-- **Derivative of the UHS Christoffel symbol**, unconditional form. -/
theorem dBmodel_uhsMetric (q : E4) (hq : 0 < q 3) (d a b : E4) :
    dBmodel uhsMetric q d a b = (q 3)⁻¹ ^ 2 • chrUHSderiv d a b := by
  refine uhsMetric_dBmodel q hq d a b ?_
  have hopen : IsOpen {q' : E4 | 0 < q' 3} := by
    rw [show {q' : E4 | 0 < q' 3} = {q' : E4 | (0 : ℝ) < coord 3 q'} from by
      ext q'; simp]
    exact isOpen_lt continuous_const (coord 3).continuous
  filter_upwards [hopen.mem_nhds hq] with q' hq'
  exact koszulChr_uhsMetric q' hq' a b

/-- **The explicit model curvature of the UHS metric.** -/
theorem modelCurv_uhsMetric (q : E4) (hq : 0 < q 3) (u v w : E4) :
    modelCurv uhsMetric q u v w = (q 3)⁻¹ ^ 2 •
      (chrUHSderiv u w v - chrUHSderiv v w u
        + chrUHSvec (chrUHSvec w v) u - chrUHSvec (chrUHSvec w u) v) := by
  rw [modelCurv, dBmodel_uhsMetric q hq, dBmodel_uhsMetric q hq]
  simp only [koszulChr_uhsMetric q hq]
  simp only [chrUHS, chrUHSvec_smul_fst, smul_smul]
  have hss : (q 3)⁻¹ * (q 3)⁻¹ = (q 3)⁻¹ ^ 2 := by ring
  rw [hss]
  module

/-- **The UHS model has non-positive sectional curvature** (indeed `K ≡ −1`). -/
theorem uhs_sec_nonpos (q : E4) (hq : 0 < q 3) (u v : E4) :
    uhsMetric q (modelCurv uhsMetric q u v v) u ≤ 0 := by
  rw [uhs_sec q hq u v]
  exact neg_nonpos.mpr (uhsMetric_gram_nonneg q u v)

end

end Work.Curvature
