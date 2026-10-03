import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.TransferUp

theorem arithIcc_sum {c : ℤ} (hc : c ≠ 0) (H : ℕ) (g : ℤ → ℂ) :
    (∑ a ∈ Work.Peluse.arithIcc c H, g a) = ∑ n ∈ Finset.Icc 1 H, g (c * (n : ℤ)) := by
  rw [Work.Peluse.arithIcc, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.cast_injective (mul_left_cancel₀ hc hab)

end Work.Peluse.TransferUp
