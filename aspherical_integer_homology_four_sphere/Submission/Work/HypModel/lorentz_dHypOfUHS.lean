import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The pullback metric of the upper half space model under `hypOfUHS`

`hypOfUHS : E4 → V5` embeds the upper half space `{q : 0 < q 3}` into the hyperboloid, and the
hyperboloid carries the Lorentz form as its Riemannian metric.  Hence the Lorentz pairing of the
derivatives `dHypOfUHS q v`, `dHypOfUHS q w` must reproduce the hyperbolic metric
`uhsMetric q v w = (q 3)⁻²⟪v,w⟫` of the upper half space model.

Both sides are explicit rational functions of the coordinates of `q`, `v`, `w` (with denominators
`q 3`), and the identity is proved by expanding into coordinates and clearing denominators.
-/

namespace Work.HypModel

open scoped Matrix InnerProductSpace

/-- The Euclidean inner product in the coordinates `0,1,2,3` of `E4`. -/
theorem inner_E4_eq_coords (q v : E4) : ⟪q, v⟫_ℝ = q 0 * v 0 + q 1 * v 1 + q 2 * v 2 + q 3 * v 3 := by
  simp [PiLp.inner_apply, Fin.sum_univ_four, mul_comm]

/-- The squared Euclidean norm in the coordinates `0,1,2,3` of `E4`. -/
theorem norm_sq_E4_eq_coords (q : E4) : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_E4_eq_coords]
  ring

theorem lorentz_dHypOfUHS {q : E4} (hq : q 3 ≠ 0) (v w : E4) :
    lorentz (dHypOfUHS q v) (dHypOfUHS q w) = uhsMetric q v w := by
  simp only [uhsMetric_apply, lorentz, dHypOfUHS_apply_zero, dHypOfUHS_apply_one,
    dHypOfUHS_apply_two, dHypOfUHS_apply_three, dHypOfUHS_apply_four,
    inner_E4_eq_coords, norm_sq_E4_eq_coords]
  field_simp
  ring

end Work.HypModel
