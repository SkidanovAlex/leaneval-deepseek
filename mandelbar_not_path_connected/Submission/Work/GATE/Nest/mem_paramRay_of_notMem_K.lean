import Mathlib
import Submission.Work.ELRig.Defs
import Submission.Work.Top.mem_paramRay_extAngle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE.Nest

/-- Every point of the dynamical plane off the filled Julia set lies on one of the external rays:
the Böttcher coordinate `dynPhi c φ` maps it into the exterior disc, and every point of the
exterior disc is of the form `‖w‖ * exp (2πiθ) = rayPoint θ ‖w‖` for a suitable angle `θ`.

This is the dynamical-plane instance (`Mb := K c`, `Φ := dynPhi c φ`) of
`Work.Top.mem_paramRay_extAngle`. -/
theorem mem_paramRay_of_notMem_K {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {z : ℂ}
    (hz : z ∉ Work.EL.K c) : ∃ ϑ : ℝ, z ∈ Work.EL.paramRay hN ϑ :=
  ⟨_, Work.Top.mem_paramRay_extAngle hN hz⟩

end Work.GATE.Nest
