import Mathlib
import Submission.Work.SeedCertRay.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- A box is the preimage of a product of closed real intervals under `z ↦ (z.re, z.im)`. -/
theorem box_toSet_eq (B : Box) :
    B.toSet = {z : ℂ | z.re ∈ Set.Icc (B.xl : ℝ) (B.xh : ℝ) ∧
      z.im ∈ Set.Icc (B.yl : ℝ) (B.yh : ℝ)} := by
  ext z
  simp [Box.toSet, Box.mem, Set.mem_Icc, and_assoc]

/-- A box with rational corners is a closed subset of the plane. -/
theorem box_isClosed (B : Work.SeedCertRay.Box) : IsClosed B.toSet := by
  rw [box_toSet_eq]
  exact (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Icc.preimage Complex.continuous_im)

end Work.SeedCertRay
