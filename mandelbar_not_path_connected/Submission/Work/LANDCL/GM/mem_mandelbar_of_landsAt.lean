import Mathlib
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LANDCL.GM

/-- **A parameter at which a dynamic ray lands lies in the mandelbar.**

`Work.Landing.landsAt c θ y` unfolds to the existence of a Böttcher coordinate of `T_c` on the
whole escaping set (`Work.ParamRays.IsDynBottcher c φ`), and
`Work.LANDCL.DynBottcherOnlyOnMandelbar` says exactly that such a coordinate exists only inside
the mandelbar.  Hence `c ∈ Mandelbar`. -/
theorem mem_mandelbar_of_landsAt (honMb : Work.LANDCL.DynBottcherOnlyOnMandelbar) {c : ℂ}
    {θ : ℝ} {y : ℂ} (h : Work.Landing.landsAt c θ y) : c ∈ LeanEval.ComplexAnalysis.Mandelbar := by
  obtain ⟨φ, hφ, _⟩ := h
  exact honMb c ⟨φ, hφ⟩

end Work.LANDCL.GM
