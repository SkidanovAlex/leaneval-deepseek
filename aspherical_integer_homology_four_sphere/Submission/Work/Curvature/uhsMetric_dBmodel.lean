import Mathlib
import Submission.Work.Curvature.Basic
import Submission.Work.Curvature.Deriv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped RealInnerProductSpace
open Filter Topology

namespace Work.Curvature

/-- **Derivative of the UHS Christoffel symbol.**  Since `chrUHS q a b = (q 3)⁻¹ • V`
with `V = chrUHSvec a b`, differentiating in the direction `d` gives
`-(q 3)⁻¹^2 * (d 3) • V`, which is exactly `(q 3)⁻¹^2 • chrUHSderiv d a b`. -/
theorem uhsMetric_dBmodel (q : E4) (hq : 0 < q 3) (d a b : E4)
    (hchr : ∀ᶠ q' in nhds q, koszulChr uhsMetric q' a b = chrUHS q' a b) :
    dBmodel uhsMetric q d a b = (q 3)⁻¹ ^ 2 • chrUHSderiv d a b := by
  have hq3 : q 3 ≠ 0 := ne_of_gt hq
  -- `koszulChr` agrees with `chrUHS` in a neighbourhood of `q`, so the derivatives
  -- agree at `q`.
  have hchr' : (fun q' : E4 => koszulChr uhsMetric q' a b) =ᶠ[nhds q]
      (fun q' : E4 => chrUHS q' a b) := hchr
  rw [dBmodel, hchr'.fderiv_eq]
  simp only [chrUHS]
  -- The scalar factor `s ↦ s⁻¹`, composed with `coord 3`.
  have hc : HasFDerivAt (fun q' : E4 => (q' 3)⁻¹)
      ((-((q 3) ^ 2)⁻¹) • coord 3) q :=
    hasFDerivAt_comp_coord (fun y : ℝ => y⁻¹) 3 q (hasDerivAt_inv hq3)
  have hV := hc.smul_const (chrUHSvec a b)
  rw [hV.fderiv]
  rw [chrUHSderiv]
  rw [ContinuousLinearMap.smulRight_apply, smul_apply, coord_apply]
  rw [smul_smul, smul_eq_mul]
  congr 1
  rw [inv_pow]
  ring

end Work.Curvature
