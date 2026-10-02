/-
# `T^[10] α₁ = α₁`: the root angle `α₁` is fixed by the tenth iterate of the angle map

The angle-doubling map of the tricorn on `ℝ` is `T θ = Int.fract (-2 * θ)` (`Work.EL.T`), and
the first root angle of the certificate is `α₁ = 371/1023` (`Work.EL.alpha1`).  Since the tenth
iterate of `T` is the fractional part of `1024 θ = (-2)^{10} θ`, and

    1024 · 371/1023 = 371 + 371/1023 = 371 + α₁,

the integer `371` disappears in the fractional part and `T^[10] α₁ = Int.fract α₁ = α₁` (as
`0 ≤ α₁ < 1`).  This is the angle-level statement behind the fact that the second return map
`F = (T_c)^{10}` of the `z₁` root-parabolic parameter preserves the `α₁`-ray.
-/
import Mathlib
import Submission.Work.SeedCertRay.Basic
import Submission.Work.ELNest.T_iterate_bAng

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

theorem T_iterate_alpha1 : Work.EL.T^[10] Work.EL.alpha1 = Work.EL.alpha1 := by
  rw [Work.ELNest.T_iterate_ten]
  have h2 : (1024 : ℝ) * Work.EL.alpha1 = (371 : ℤ) + 371 / 1023 := by
    rw [Work.EL.alpha1]; norm_num
  rw [h2, Int.fract_intCast_add,
    Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩, Work.EL.alpha1]

end Work.SeedCertRay
