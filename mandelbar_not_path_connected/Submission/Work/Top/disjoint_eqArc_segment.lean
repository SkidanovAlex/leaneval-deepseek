import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.eqArc_subset_potential

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

/-- The equipotential arc at level `R > 1` lies in the level set `{potential = log R}`, while the
segment `segment ℝ x y` lies in the sublevel set `{potential < log R}`; hence the two are disjoint.

This is the elementary "arcs and level sets do not meet" step of the endgame: the segment `x y`
stays strictly inside the equipotential of level `R`, so it cannot touch the arc of that level.

(We do not even need `Φ` to be injective or `Mb` compact here: the statement is purely about the
potential, which is why it holds verbatim from `eqArc_subset_potential`.) -/
theorem disjoint_eqArc_segment {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    {β₁ β₂ R : ℝ} {x y : ℂ} (hR : 1 < R)
    (hseg : ∀ c ∈ segment ℝ x y, Work.Top.potential Mb Φ c < Real.log R) :
    Disjoint (Work.Top.NakaneData.eqArc hN β₁ β₂ R) (segment ℝ x y) := by
  rw [Set.disjoint_left]
  intro c hc hct
  have h1 : Work.Top.potential Mb Φ c = Real.log R :=
    eqArc_subset_potential hN hR hc
  have h2 : Work.Top.potential Mb Φ c < Real.log R := hseg c hct
  linarith

end Work.Top
