import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELRig.rayTail_lift
import Submission.Work.LandLeaves.TypeGeometry

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar)

/-- The angle doubling map `Work.Landing.angDouble` of the landing theory is the same function
as the angle map `Work.EL.T` of the EL area: both are `θ ↦ Int.fract (-2 θ)`. -/
theorem angDouble_eq_T : Work.Landing.angDouble = Work.EL.T := rfl

/-- The iterate exponents agree: `4 ^ k = 2 ^ (2 k)`. -/
theorem four_pow_eq_two_pow (k : ℕ) : (4 : ℕ) ^ k = 2 ^ (2 * k) := by
  rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, pow_mul]

theorem rayPt_iterate_angDouble {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) {k : ℕ} {θ t : ℝ} (ht : 1 < t) :
    Work.EL.rayPt hN ((Work.Landing.angDouble)^[2 * k] θ) (t ^ (4 ^ k : ℕ))
      = (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (Work.EL.rayPt hN θ t) := by
  have h := Work.ELRig.rayPt_iterate_antibar hN hφ (θ := θ) ht (2 * k)
  rw [h]
  rw [show (4 : ℕ) ^ k = 2 ^ (2 * k) from four_pow_eq_two_pow k]
  rfl

end Work.LandLeaves
