import Mathlib
import Submission.Work.RTOwed.reflWallDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-- **The reflection of a vertical wall of the upper half space model is the Lorentz
transformation `wallMat k c`.**

For a point `z` of the upper half space model (`z 3 ≠ 0`) and the reflection `reflWall4 k c`
of the `k`-th horizontal coordinate in the wall `{z k = c}`, the hyperboloid representatives are
related by the Lorentz matrix `wallMat k c`:

`Π(reflWall4 k c z) = wallMat k c *ᵥ Π(z)`.

Coordinatewise, with `λ = 2 (z k - c) / z 3` one has `wallMat k c *ᵥ P = P - λ n_{k,c}` where
`n_{k,c} = e_k + c e_3 + c e_4`; the `k`-th coordinate becomes `(2c - z k)/z 3`, the height
coordinates use `‖reflWall4 k c z‖² = ‖z‖² + 4c² - 4c z k`, and all other coordinates are
unchanged. -/
theorem hypOfUHS_reflWall4 (k : Fin 3) (c : ℝ) (z : Work.Cusp.E4) (hz : z 3 ≠ 0) :
    Work.HypModel.hypOfUHS (Work.RTOwed.reflWall4 k c z)
      = Matrix.mulVec (Work.RTOwed.wallMat k c) (Work.HypModel.hypOfUHS z) := by
  funext j
  rw [wallMat_mulVec_apply]
  fin_cases k <;> fin_cases j <;>
    simp [Work.HypModel.hypOfUHS_apply_zero, Work.HypModel.hypOfUHS_apply_one,
      Work.HypModel.hypOfUHS_apply_two, Work.HypModel.hypOfUHS_apply_three,
      Work.HypModel.hypOfUHS_apply_four, reflWall4_apply, wallVec, FoldInst.f3to5,
      norm_sq_reflWall4] <;> field_simp <;> ring

end Work.RTOwed
