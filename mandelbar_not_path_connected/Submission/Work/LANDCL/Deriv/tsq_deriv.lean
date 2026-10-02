import Mathlib
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LANDCL.Deriv

/-- The derivative of the holomorphic second iterate
`Tsq c z = (z^2 + c̄)^2 + c` of the antiholomorphic quadratic `T_c`:
`deriv (Tsq c) z = 4 z (z^2 + c̄)`. -/
theorem tsq_deriv (c z : ℂ) :
    deriv (Work.Landing.Tsq c) z = 4 * z * (z ^ 2 + star c) := by
  have h : HasDerivAt (Work.Landing.Tsq c) (4 * z * (z ^ 2 + star c)) z := by
    unfold Work.Landing.Tsq
    have h1 : HasDerivAt (fun w : ℂ => w ^ 2 + star c) (2 * z) z := by
      simpa using ((hasDerivAt_id z).pow 2).const_add (star c)
    have h3 : HasDerivAt (fun w : ℂ => (w ^ 2 + star c) ^ 2 + c)
        (↑2 * (z ^ 2 + star c) ^ (2 - 1) * (2 * z)) z := (h1.pow 2).add_const c
    convert h3 using 1
    norm_num
    ring
  exact h.deriv

end Work.LANDCL.Deriv
