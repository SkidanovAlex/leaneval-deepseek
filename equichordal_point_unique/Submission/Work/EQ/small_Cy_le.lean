import Mathlib
import Submission.Work.EQ.hetero_leaf

namespace Work.EQ

theorem small_Cy_le {a : ℝ} (d : Work.EQ.LocData a) {y : ℝ} (hs : d.Small y) :
    d.C * y ≤ d.κ * (1 - d.κ) ^ 2 / 16 := by
  have h2 : 2 * d.C * y / (1 - d.κ) ^ 2 ≤ d.κ / 8 := hs.2
  have hpos : 0 < (1 - d.κ) ^ 2 := pow_pos d.one_sub_pos 2
  rw [div_le_iff₀ hpos] at h2
  nlinarith [h2]

end Work.EQ
