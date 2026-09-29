import Mathlib

namespace Work.C17I

theorem hasSum_tsum_of_coeff_growth {c : ℕ → ℂ} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r)
    (hc : ∀ n : ℕ, ‖c n‖ ≤ C * r ^ n) :
    ∀ z : ℂ, ‖z‖ < 1 / r → HasSum (fun n : ℕ => c n * z ^ n) (∑' n : ℕ, c n * z ^ n) := by
  intro z hz
  have _hC : (0 : ℝ) ≤ C := hC
  -- From ‖z‖ < 1/r and r > 0 we get ‖z‖ * r < 1.
  have hzr : ‖z‖ * r < 1 := by
    rw [lt_div_iff₀ hr] at hz
    linarith
  have hnn : 0 ≤ ‖z‖ * r := by positivity
  -- The dominating geometric series C * (‖z‖ * r)^n is summable.
  have hsum : Summable (fun n : ℕ => C * (‖z‖ * r) ^ n) :=
    (summable_geometric_of_lt_one hnn hzr).mul_left C
  -- Termwise domination.
  have hbound : ∀ n : ℕ, ‖c n * z ^ n‖ ≤ C * (‖z‖ * r) ^ n := by
    intro n
    rw [norm_mul, norm_pow]
    calc ‖c n‖ * ‖z‖ ^ n ≤ (C * r ^ n) * ‖z‖ ^ n :=
          mul_le_mul_of_nonneg_right (hc n) (by positivity)
      _ = C * (‖z‖ * r) ^ n := by rw [mul_pow]; ring
  exact (Summable.of_norm_bounded hsum hbound).hasSum

end Work.C17I
