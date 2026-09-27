import Mathlib
import Submission.Work.EKLC6Core.InjRadius
import Submission.Work.EKLC6Core.cut_defs
import Submission.Work.EKLC6Core.injCap_smul_le

namespace Work.EKLC6Core

open Work.EKLContract

/-- **Upper Lipschitz bound for the injectivity radius.**
`X3 = SL3(R)/SL3(Z)`, `V r = {g : |g i j - 1 i j| < r}` (max-entry displacement), `Vball r y = V r • y`,
`injCap x = min (injS x) (1/2)` where `injS x = sSup {t : 0 < t ∧ t ≤ 1 ∧ InjAt x t}` and
`InjAt x t` says `v ↦ v • x` is injective on `V t`.

Claim: moving a point by a displacement small compared with its *own* injectivity radius can
increase the (capped) injectivity radius by at most a factor `2^19`.

Proof route: first an upper bound for `injS` alone, `injS z ≤ C * (r + injS y)` for `z ∈ V r • y`
with `r ≤ 1/2`: if `¬ InjAt y t` then there is `h ≠ 1` with `h ∈ V (2t+3t^2)` and `h • y = y`
(h = v₂⁻¹v₁); conjugating by `u ∈ V r` gives `w := u * h * u⁻¹ ≠ 1` with
`w ∈ V (30r + 2t+3t² + 3·(30r)(2t+3t²))` and `w • z = z`, so `¬ InjAt z τ` for `τ` at least that
quantity; let `t ↓ injS y` and bound using `injS y ≤ 1`, `r ≤ 1/2`. Then split on
`injS y ≤ 1/2` vs `injS y > 1/2`: in the second case `injCap y = 1/2 ≥ injCap z`. -/
theorem injCap_le_mul_of_mem_Vball {z y : Work.EKLContract.X3} {r : ℝ} (hr : 0 ≤ r)
    (hr8 : r ≤ Work.EKLC6Core.injCap y / 8)
    (hz : z ∈ Work.EKLComp.Vball r y) :
    Work.EKLC6Core.injCap z ≤ 2 ^ 19 * Work.EKLC6Core.injCap y := by
  obtain ⟨u, hu, rfl⟩ := Work.EKLComp.mem_Vball.mp hz
  -- `V r` is nonempty, so the displacement is positive; and it is at most `1/2`.
  have hr_pos : 0 < r := lt_of_le_of_lt (abs_nonneg _) (hu 0 0)
  have hr_half : r ≤ 1 / 2 := by have := injCap_le_half y; linarith
  have hle : injCap (u • y) ≤ 4 * injCap y := injCap_smul_le hr_pos hr_half hr8 hu
  have hy : (0 : ℝ) ≤ injCap y := le_of_lt (injCap_pos y)
  have h4 : (4 : ℝ) ≤ 2 ^ 19 := by norm_num
  calc injCap (u • y) ≤ 4 * injCap y := hle
    _ ≤ 2 ^ 19 * injCap y := mul_le_mul_of_nonneg_right h4 hy

end Work.EKLC6Core
