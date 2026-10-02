import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELTop.Defs
import Submission.Work.LandLeaves.ccBet_angDouble_of_typeSet_short
import Submission.Work.LandLeaves.ccBet_angDouble_of_typeSet_long

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- **Cyclic-order preservation by the return angle map.**  If the dynamic rays at three angles
`a`, `b`, `x` all accumulate at the repelling periodic point `y` (`IsRepelling c k y`) and `x`
lies strictly counterclockwise between `a` and `b` (`ccBet a b x`), then the same is true of the
images under the `2k`-fold angle map `(angDouble)^[2k] = θ ↦ Int.fract (4^k θ)`.

The two cases `4^k * fract (b - a) ≤ 1` (the *short* arc, pure `Int.fract` arithmetic) and
`1 < 4^k * fract (b - a)` (the *long* arc, which uses the plane topology of the external rays)
are separated here. -/
theorem ccBet_angDouble_of_typeSet {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {a b x : ℝ} (ha : Work.Landing.rayAccum c φ a = {y})
    (hb : Work.Landing.rayAccum c φ b = {y}) (hx : Work.Landing.rayAccum c φ x = {y})
    (hab : Work.LandLeaves.ccBet a b x) :
    Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b) ((Work.Landing.angDouble)^[2 * k] x) := by
  by_cases h : (4 : ℝ) ^ k * Int.fract (b - a) ≤ 1
  · exact ccBet_angDouble_of_typeSet_short hφ hrep ha hb hx h hab
  · exact ccBet_angDouble_of_typeSet_long hφ hrep ha hb hx (lt_of_not_ge h) hab

end Work.LandLeaves
