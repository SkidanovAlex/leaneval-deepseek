import Mathlib
import Submission.Work.HP.badclass.BadDefs

set_option autoImplicit false
noncomputable section

open MvPolynomial Finset

namespace Work.HP.badclass

/-- The number of torus points collinear with a fixed `x` is at most `p`. -/
theorem resonant_card (n p : ℕ) [NeZero p] (x : Fin (n + 1) → ZMod p) :
    ((Work.HP.torFinset n p).filter (fun y => ∃ z : ZMod p, y = z • x)).card ≤ p := by
  classical
  calc ((Work.HP.torFinset n p).filter (fun y => ∃ z : ZMod p, y = z • x)).card
      ≤ ((Finset.univ : Finset (ZMod p)).image (fun z => z • x)).card := by
        apply Finset.card_le_card
        intro y hy
        rw [Finset.mem_filter] at hy
        obtain ⟨z, rfl⟩ := hy.2
        exact Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩
    _ ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_image_le
    _ = p := by simp [ZMod.card]

end Work.HP.badclass
