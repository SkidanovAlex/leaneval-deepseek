import Mathlib
import Submission.Work.EQ.FanTri.SecOrderDefs

namespace Work.EQ.FanTri

/-- Exact factorisation of the difference of squares of `sR`: on the ball `‖z‖, ‖w‖ ≤ sHat a/16`
(`sR a z ^ 2 = sD a z ^ 2 + z.2 ^ 2` by `sD_sR_setup`), the difference `sR a z ^ 2 - sR a w ^ 2`
equals `-(z.1 - w.1) * (sD a z + sD a w) + (z.2 - w.2) * (z.2 + w.2)`. -/
theorem sR_sq_diff_factor {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z w : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) (hw : ‖w‖ ≤ sHat a / 16) :
    (sR a z - sR a w) * (sR a z + sR a w) =
      -(z.1 - w.1) * (sD a z + sD a w) + (z.2 - w.2) * (z.2 + w.2) := by
  -- On the ball, `sR` squares back to `D² + z₂²` (`sD_sR_setup`).
  have hz' := (sD_sR_setup ha0 ha1 hz).2.2.2.2.2
  have hw' := (sD_sR_setup ha0 ha1 hw).2.2.2.2.2
  have h1 : (sR a z - sR a w) * (sR a z + sR a w) = sR a z ^ 2 - sR a w ^ 2 := by ring
  rw [h1, hz', hw']
  -- `z.1 - w.1 = sD a w - sD a z`, and the rest is a polynomial identity in `sD`, `z.2`, `w.2`.
  simp only [sD]
  ring

end Work.EQ.FanTri
