import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-- The tangent vector `dHypOfUHS q v` to the hyperboloid at the point `hypOfUHS q` is
Lorentz-orthogonal to `hypOfUHS q`: the hyperboloid is the level set `⟨x,x⟩ = -1`. -/
theorem tangent_hypOfUHS {q : E4} (hq : q 3 ≠ 0) (v : E4) :
    lorentz (hypOfUHS q) (dHypOfUHS q v) = 0 := by
  have hnorm : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_four]
  have hinner : ⟪q, v⟫_ℝ = q 0 * v 0 + q 1 * v 1 + q 2 * v 2 + q 3 * v 3 := by
    rw [inner_eq_dotProduct]
    simp [dotProduct, Fin.sum_univ_four]
  rw [lorentz]
  simp only [hypOfUHS_apply_zero, hypOfUHS_apply_one, hypOfUHS_apply_two,
    hypOfUHS_apply_three, hypOfUHS_apply_four,
    dHypOfUHS_apply_zero, dHypOfUHS_apply_one, dHypOfUHS_apply_two,
    dHypOfUHS_apply_three, dHypOfUHS_apply_four, hinner, hnorm]
  field_simp
  ring

end Work.HypModel
