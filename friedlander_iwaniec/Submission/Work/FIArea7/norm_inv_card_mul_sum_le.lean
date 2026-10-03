import Mathlib

namespace Work.FIArea7

theorem norm_inv_card_mul_sum_le {G : Type*} [CommGroup G] [Fintype G]
    (H : AddChar (Additive G) ℂ → ℂ) {B C : ℝ} (hH : ∀ χ, ‖H χ‖ ≤ C * B ^ 2) :
    ‖(1 / (Fintype.card G : ℂ)) * ∑ χ : AddChar (Additive G) ℂ, H χ‖ ≤ C * B ^ 2 := by
  -- There are exactly `card G` complex additive characters of the finite abelian group `G`.
  have hcard : Fintype.card (AddChar (Additive G) ℂ) = Fintype.card G := by
    simp
  -- Bound the unnormalised sum of the `H χ` by `card G` times the pointwise bound.
  have hS : ‖∑ χ : AddChar (Additive G) ℂ, H χ‖ ≤ (Fintype.card G : ℝ) * (C * B ^ 2) := by
    calc ‖∑ χ : AddChar (Additive G) ℂ, H χ‖ ≤ ∑ χ, ‖H χ‖ := norm_sum_le _ _
      _ ≤ ∑ χ : AddChar (Additive G) ℂ, (C * B ^ 2) := Finset.sum_le_sum (fun χ _ => hH χ)
      _ = (Fintype.card (AddChar (Additive G) ℂ) : ℝ) * (C * B ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = (Fintype.card G : ℝ) * (C * B ^ 2) := by rw [hcard]
  rw [norm_mul]
  have hnorm : ‖(1 / (Fintype.card G : ℂ))‖ = 1 / (Fintype.card G : ℝ) := by
    rw [one_div, norm_inv, Complex.norm_natCast, one_div]
  rw [hnorm]
  calc 1 / (Fintype.card G : ℝ) * ‖∑ χ : AddChar (Additive G) ℂ, H χ‖
      ≤ 1 / (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) * (C * B ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hS
        positivity
    _ = C * B ^ 2 := by
        have hN : (Fintype.card G : ℝ) ≠ 0 := by
          exact_mod_cast Fintype.card_ne_zero
        field_simp

end Work.FIArea7
