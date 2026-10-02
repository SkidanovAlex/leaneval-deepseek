/-
# The Jordan curve theorem, discharged

`Work.Top.JordanForm` (`Submission/Work/Top/Jordan.lean`) is the plane-topological input of the
mandelbar endgame:

  the complement of a Jordan curve `C ⊆ ℂ` has exactly two components `I`, `O`, one bounded and
  one unbounded, each having `C` as its frontier.

This file proves it, from the commons Jordan curve theorem
(`Commons.Topology.Jordan.plane_separation`, `Commons.Topology.Connected.
frontier_component_compl_range`), so that `Work.Top.JordanForm` is no longer a hypothesis.
-/
import Mathlib
import Submission.Work.Top.Jordan
import Submission.Work.TopJordan.Sides

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open Set

namespace Work.TopJordan

noncomputable section

/-- **The Jordan curve theorem**: `Work.Top.JordanForm` holds. -/
theorem jordanForm : Work.Top.JordanForm := by
  intro C hC
  let S := sidesOf hC
  exact ⟨S.I, S.O, S.isOpen_I, S.isOpen_O, S.union_eq, S.disjoint, S.preconnected_I,
    S.preconnected_O, S.bounded_I, S.unbounded_O, S.frontier_I, S.frontier_O⟩

end

end Work.TopJordan
