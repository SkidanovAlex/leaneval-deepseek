import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat

namespace Commons.Data.Nat

theorem card_pi_Ico_fin {p Q t : ℕ} (hQp : Q ≤ p) (u : Fin t → Fin Q) :
    (Finset.univ.filter (fun v : Fin t → Fin p =>
        ∀ j, (u j).val * p / Q ≤ (v j).val ∧ (v j).val < ((u j).val + 1) * p / Q)).card
      = ∏ j, (((u j).val + 1) * p / Q - (u j).val * p / Q) := by
  have key : (Finset.univ.filter (fun v : Fin t → Fin p =>
        ∀ j, (u j).val * p / Q ≤ (v j).val ∧ (v j).val < ((u j).val + 1) * p / Q))
      = Fintype.piFinset (fun j : Fin t => Finset.univ.filter (fun y : Fin p =>
          (u j).val * p / Q ≤ y.val ∧ y.val < ((u j).val + 1) * p / Q)) := by
    ext v
    simp [Fintype.mem_piFinset]
  rw [key, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro j _
  have hb_le : ((u j).val + 1) * p / Q ≤ p := by
    rcases Nat.eq_zero_or_pos Q with hQ | hQ
    · subst hQ; simp
    · calc ((u j).val + 1) * p / Q ≤ Q * p / Q := by
            apply Nat.div_le_div_right
            apply Nat.mul_le_mul_right
            exact Nat.succ_le_of_lt (u j).isLt
        _ = p := by rw [Nat.mul_div_right _ hQ]
  have himg : (Finset.univ.filter (fun y : Fin p =>
        (u j).val * p / Q ≤ y.val ∧ y.val < ((u j).val + 1) * p / Q)).image (fun y => y.val)
      = Finset.Ico ((u j).val * p / Q) (((u j).val + 1) * p / Q) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · rintro ⟨hxa, hxb⟩
      exact ⟨⟨x, lt_of_lt_of_le hxb hb_le⟩, ⟨hxa, hxb⟩, rfl⟩
  calc (Finset.univ.filter (fun y : Fin p =>
        (u j).val * p / Q ≤ y.val ∧ y.val < ((u j).val + 1) * p / Q)).card
      = ((Finset.univ.filter (fun y : Fin p =>
        (u j).val * p / Q ≤ y.val ∧ y.val < ((u j).val + 1) * p / Q)).image (fun y => y.val)).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = (Finset.Ico ((u j).val * p / Q) (((u j).val + 1) * p / Q)).card := by rw [himg]
    _ = ((u j).val + 1) * p / Q - (u j).val * p / Q := Nat.card_Ico _ _

end Commons.Data.Nat