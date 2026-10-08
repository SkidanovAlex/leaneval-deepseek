import Submission.Work.ZassenhausSuzuki.QSZPrelim
import Submission.Work.ZassenhausSuzuki.HigmanGap.suzuki_class_two_squares

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The exponent of a Suzuki `2`-group

`Work.ZassenhausSuzuki.suzuki_pow_four_eq_one`: in a Suzuki two-group every element has order
dividing `4` (Higman: `Q` has class `2` and its squares are central, so `x⁴ = (x²)² = 1`).

The dependency is the *local* copy `Submission.Work.ZassenhausSuzuki.HigmanGap.suzuki_class_two_squares`
(identical to `Submission.Work.Higman.suzuki_class_two_squares`, except that it routes through the
local copy of Higman's Theorem 1 used to unblock the workspace's Higman area).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-- In a Suzuki two-group every element has order dividing `4`. -/
theorem suzuki_pow_four_eq_one {Q : Subgroup G} (hSuz : IsSuzukiTwoGroup ↥Q) :
    ∀ x : ↥Q, x ^ 4 = 1 := by
  obtain ⟨h2g⟩ := (Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp (P := ↥Q)).mp hSuz
  obtain ⟨-, hsq⟩ := Work.ZassenhausSuzuki.HigmanLocal.suzuki_class_two_squares h2g
  intro x
  have hx : x ^ 2 ∈ Subgroup.center ↥Q := hsq x
  have h4 : x ^ 2 * x ^ 2 = 1 := Work.Higman.center_sq_eq_one h2g (x ^ 2) hx
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two]
  exact h4

end Work.ZassenhausSuzuki
