import Mathlib
import Submission.Work.BridgeSquare.CuspPair

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.BridgeSquare

/-- **The section is a section of the projection**: the projection `projBdry` forgetting the
boundary coordinate (`Work.BridgeSquare.projMap`), composed with the section
`y ↦ ⟨y.1, (p₀, y.2)⟩` (`Work.BridgeSquare.secMap`) at any basepoint `p₀` of the square boundary,
is the identity.  Both maps are given on `Σ`-points, so this is a definitional identity. -/
theorem secMap_projMap [rt : Work.Space.RTData] (p₀ : Work.Space.Split.BdryPt)
    (y : Work.BridgeSquare.Top (rt := rt)) :
    Work.BridgeSquare.projMap (rt := rt) (Work.BridgeSquare.secMap (rt := rt) p₀ y) = y := by
  rfl

end Work.BridgeSquare
