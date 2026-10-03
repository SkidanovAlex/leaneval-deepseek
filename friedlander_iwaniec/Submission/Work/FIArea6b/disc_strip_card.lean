import Mathlib
import Submission.Work.FIArea6b.conv_hull_card_le
import Submission.Work.FIArea6b.convexHull_volume_le

namespace Work.FIArea6b

open MeasureTheory

theorem disc_strip_card (r s : ℤ) (hne : r ≠ 0 ∨ s ≠ 0) (R W : ℝ) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (c : ℝ × ℝ) (A : Finset (ℤ × ℤ))
    (hball : ∀ x ∈ A, ((x.1 : ℝ) - c.1) ^ 2 + ((x.2 : ℝ) - c.2) ^ 2 ≤ R ^ 2)
    (hstrip : ∀ x ∈ A, |(r : ℝ) * (x.2 : ℝ) - (s : ℝ) * (x.1 : ℝ)| ≤ W) :
    (A.card : ℝ) ≤ (2 * R + 1) * (2 * W / Real.sqrt ((r : ℝ) ^ 2 + (s : ℝ) ^ 2) + 1) := by
  have h1 := conv_hull_card_le r s hne R W hR hW c A hball hstrip
  have h2 := convexHull_volume_le r s hne R W hR hW c A hball hstrip
  have h3 : (A.card : ℝ) ≤ 4 * R * (W / Real.sqrt ((r : ℝ) ^ 2 + (s : ℝ) ^ 2))
      + 2 * R + 2 * W / Real.sqrt ((r : ℝ) ^ 2 + (s : ℝ) ^ 2) + 1 := by
    linarith [h1, h2]
  rw [show (2 * R + 1) * (2 * W / Real.sqrt ((r : ℝ) ^ 2 + (s : ℝ) ^ 2) + 1)
      = 4 * R * (W / Real.sqrt ((r : ℝ) ^ 2 + (s : ℝ) ^ 2))
        + 2 * R + 2 * W / Real.sqrt ((r : ℝ) ^ 2 + (s : ℝ) ^ 2) + 1 from by ring]
  exact h3

end Work.FIArea6b
