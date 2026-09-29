import Mathlib

namespace Work.C17g

theorem lipschitz_of_local_bound {E : Type*} [SeminormedAddCommGroup E] {f : ℂ → E} {T : Set ℂ}
    {r Cc B : ℝ} (hr : 0 < r) (hC : 0 ≤ Cc) (hB : 0 ≤ B)
    (hloc : ∀ x ∈ T, ∀ y ∈ T, ‖y - x‖ < r → ‖f y - f x‖ ≤ Cc * ‖y - x‖)
    (hbd : ∀ x ∈ T, ‖f x‖ ≤ B) :
    LipschitzOnWith (Real.toNNReal (max Cc (2 * B / r))) f T := by
  refine LipschitzOnWith.of_dist_le' fun x hx y hy => ?_
  rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (f x) (f y), norm_sub_rev x y]
  rcases lt_or_ge ‖y - x‖ r with h | h
  · calc ‖f y - f x‖ ≤ Cc * ‖y - x‖ := hloc x hx y hy h
      _ ≤ max Cc (2 * B / r) * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · have h2B : ‖f y - f x‖ ≤ 2 * B := by
      have hy' := hbd y hy
      have hx' := hbd x hx
      calc ‖f y - f x‖ ≤ ‖f y‖ + ‖f x‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add hy' hx'
        _ = 2 * B := by ring
    have hkey : 2 * B ≤ max Cc (2 * B / r) * ‖y - x‖ := by
      have hpos : 0 ≤ 2 * B / r := div_nonneg (by linarith) (le_of_lt hr)
      have hrne : r ≠ 0 := ne_of_gt hr
      calc 2 * B = (2 * B / r) * r := by rw [div_mul_cancel₀ _ hrne]
        _ ≤ (2 * B / r) * ‖y - x‖ := mul_le_mul_of_nonneg_left h hpos
        _ ≤ max Cc (2 * B / r) * ‖y - x‖ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    linarith

end Work.C17g
