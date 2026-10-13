import Mathlib
import Submission.Work.WilE7.Defs

namespace Work.WilE7

theorem cylImage_card {n M : ℕ} (C : Finset (Set (Fin (n + M) → ℝ))) :
    (Work.WilE7.cylImage n M C).card ≤ C.card := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [cylImage]
    exact le_trans (ih _) Finset.card_image_le

end Work.WilE7
