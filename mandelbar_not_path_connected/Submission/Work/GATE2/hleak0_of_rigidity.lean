import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.ELRig.rigidity

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The equator leak, from the rigidity inputs.**  The equator-curve rigidity
(`Work.ELRig.rigidity`) says that the equator `Ψ '' ℝ` of the repelling coordinate cannot be
contained in the filled Julia set, given the petal condition at the flower's `Ψ_ends` level (a
field of `ParabolicFlower`), the deep real tail in the near side of the `α`-pair, and the tripod
data at `b₂`.  This is the `∃ x, Ψ x ∉ K c` form consumed by the case-(ii) drive. -/
theorem hleak0_of_rigidity {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa)
    (htail : ∃ R' : ℝ, ∀ x : ℝ, x < -R' →
      fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear nest.P0)
    (tr : Work.EL.B2Data d.hN d.z₁) :
    ∃ x : ℝ, fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c := by
  -- The far ends of the repelling half-planes are the `hγ` input of the rigidity:
  -- this is precisely the `Ψ_ends` field of the flower.
  obtain ⟨R₀, hR₀⟩ := fl.Ψ_ends
  by_contra h
  push Not at h
  exact Work.ELRig.rigidity d fl nest hR₀ htail tr h

end Work.GATE2
