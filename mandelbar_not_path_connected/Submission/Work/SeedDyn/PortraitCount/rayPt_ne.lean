import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.ELPull.Defs
import Submission.Work.Top.rayPt_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn.PortraitCount

/-- Ray points of the dynamical Böttcher coordinate at a fixed level `t > 1` are injective in
the angle modulo `1`: if the two angles have different fractional parts, the ray points differ. -/
theorem rayPt_ne {c : ℂ} (hN : Work.ELPull.DynB c) {θ' θ'' t : ℝ}
    (ht : 1 < t) (h : Int.fract θ' ≠ Int.fract θ'') :
    hN.rayPt θ' t ≠ hN.rayPt θ'' t := by
  intro heq
  -- The ray point only depends on the angle modulo `1`.
  have h₁ := Work.ELPull.rayPt_fract_eq hN θ' t ht
  have h₂ := Work.ELPull.rayPt_fract_eq hN θ'' t ht
  have hmain : hN.rayPt (Int.fract θ') t = hN.rayPt (Int.fract θ'') t := by
    rw [h₁, heq, ← h₂]
  -- Both fractional parts lie in `[0,1)`, so injectivity of the ray point gives equality.
  have hinj := Work.Top.rayPt_injOn hN (Int.fract_nonneg θ') (Int.fract_lt_one θ')
    (Int.fract_nonneg θ'') (Int.fract_lt_one θ'') ht ht hmain
  exact h hinj.1

end Work.SeedDyn.PortraitCount
