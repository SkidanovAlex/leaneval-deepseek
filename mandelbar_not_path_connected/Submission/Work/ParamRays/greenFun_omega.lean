/-
# Rotational invariance of the Green function

The rotation `z ↦ ω z` conjugates the dynamics `T_c` to `T_{ω c}`
(`Work.ParamRays.Tantibar_omega`), so it maps the orbit of `w` under `T_c` to the
orbit of `ω w` under `T_{ω c}`.  Since `‖ω‖ = 1`, the norms of the orbits agree,
and because `greenSeq` is built purely from these norms, the Green function is
invariant: `greenFun (ω c) (ω w) = greenFun c w`.
-/
import Mathlib
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.Green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ParamRays

/-- The normalized logarithms of the orbit are invariant under the rotation
`z ↦ ω z` acting on both the parameter and the point. -/
theorem greenSeq_omega (c w : ℂ) (n : ℕ) :
    greenSeq (omega * c) (omega * w) n = greenSeq c w n := by
  simp only [greenSeq]
  rw [orbit_omega, norm_mul, norm_omega, one_mul]

/-- The Green function is invariant under the rotation `z ↦ ω z`:
`greenFun (ω * c) (ω * w) = greenFun c w`. -/
theorem greenFun_omega (c w : ℂ) :
    Work.ParamRays.greenFun (Work.ParamRays.omega * c) (Work.ParamRays.omega * w) = Work.ParamRays.greenFun c w := by
  have h : greenSeq (omega * c) (omega * w) = greenSeq c w :=
    funext fun n => greenSeq_omega c w n
  rw [greenFun, greenFun, h]

end Work.ParamRays
