import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- For a point `q` of the upper half space chart (`q 3 ≠ 0`), the lift `hypOfUHS q` lies on the
hyperboloid: `⟨hypOfUHS q, hypOfUHS q⟩ = -1`. -/
theorem lorentz_hypOfUHS_self {q : E4} (hq : q 3 ≠ 0) :
    lorentz (hypOfUHS q) (hypOfUHS q) = -1 := by
  have hnorm : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_four]
  rw [lorentz]
  simp only [hypOfUHS_apply_zero, hypOfUHS_apply_one, hypOfUHS_apply_two,
    hypOfUHS_apply_three, hypOfUHS_apply_four]
  rw [hnorm]
  field_simp
  ring

end Work.HypModel
