import Mathlib
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.TorsorExistence.cls_eq_zero_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- **The local-obstruction criterion.**  If an additive homomorphism `φ` out of `E(L)` kills the
image of the shift `σ - 1` but not the marked point `P`, then the twist is pointless.  This is the
abstract form of the paper's reduction-modulo-a-place argument: `φ` is the reduction map at a place
at which `L/𝕜` is inert (so `σ` acts trivially on the residue field) and `E` has good reduction. -/
theorem pointless_of_shift_mem_ker {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)
    {G : Type*} [AddCommGroup G] (φ : D.LPoints →+ G) (hP : φ D.PL ≠ 0)
    (hker : ∀ x : D.LPoints, φ (D.shift x) = 0) : D.Pointless := by
  -- `D.Pointless` is `D.cls ≠ 0`, and `D.cls = 0` holds exactly when `D.PL` is in the image
  -- of the shift `σ - 1`, which `φ` annihilates.
  show D.cls ≠ 0
  intro h
  rw [Work.TorsorExistence.cls_eq_zero_iff D] at h
  obtain ⟨R, hR⟩ := h
  exact hP (by rw [← hR, hker R])

end Work.PointlessIndexFive
