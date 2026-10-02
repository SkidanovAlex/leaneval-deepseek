import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.ccBet_v2_defs
import Submission.Work.LandLeaves.gmLocalOrder
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.ELTop.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A `sorry`-free copy of `landsN_of_rayAccum'`

`Submission/Work/LandLeaves/InArcHard/Basic.lean` states `landsN_of_rayAccum'`, but its import
of `ray_subset_pairSide_angMul` draws in the (still `sorry`-bearing) hard case
`ccBet_angDouble_of_hard_case`, so any module that imports it cannot pass an axiom check.  The
one-line statement is reproduced here on top of `sorry`-free imports only, under the same name
and namespace, so that a module needing it can import *this* module instead.
-/
namespace Work.LandLeaves.InArcHard

/-- The `Work.EL` landing statement attached to a `rayAccum` singleton at `y`. -/
theorem landsN_of_rayAccum' {c : ℂ} {φ : ℂ → ℂ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) {θ : ℝ}
    (h : Work.Landing.rayAccum c φ θ = {y}) :
    Work.EL.LandsN (Work.LandLeaves.dynBNakane hφ) θ y :=
  (Work.ELTop.landsN_iff_landsAt (Work.LandLeaves.dynBNakane hφ) hφ θ y).mpr
    (Work.LandLeaves.landsAt_of_rayAccum hφ h)

end Work.LandLeaves.InArcHard
