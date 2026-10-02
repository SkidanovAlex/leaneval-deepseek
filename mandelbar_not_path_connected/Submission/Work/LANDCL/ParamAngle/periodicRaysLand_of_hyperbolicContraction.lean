import Mathlib
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LANDCL.ParamAngle

/-- **The hyperbolic (Douady–Hubbard) contraction input yields the landing of all periodic
rays.**

`Work.LANDCL.HyperbolicContraction c` is, by definition, the pair consisting of a Böttcher
coordinate `φ` of `T_c` which is a homeomorphism onto the exterior of the unit disk
(`Work.Landing.IsDynBottcherHomeo c φ`) and the continuous extension of its inverse to the
closed exterior of the unit disk (`Work.Landing.InverseBottcherExtends c φ`).  Those are exactly
the two hypotheses of `Work.Landing.PeriodicRaysLand_of_extension`, which produces the landing
point of every periodic ray.  So the reduction is the projection of the existential hypothesis
followed by that theorem. -/
theorem periodicRaysLand_of_hyperbolicContraction {c : ℂ} (h : Work.LANDCL.HyperbolicContraction c) :
    Work.Landing.PeriodicRaysLand c := by
  obtain ⟨φ, hhom, hext⟩ := h
  exact Work.Landing.PeriodicRaysLand_of_extension hhom hext

end Work.LANDCL.ParamAngle
