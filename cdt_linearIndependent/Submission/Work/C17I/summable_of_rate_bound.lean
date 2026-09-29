import Mathlib

namespace Work.C17I

/-- If the coefficients `c k` grow at most like `C / R ^ k` (i.e. `‖c k‖ * R ^ k ≤ C` with
`R > 0`), then for any `z` with `‖z‖ < R` the power series `∑ c k * z ^ k` converges. -/
theorem summable_of_rate_bound {c : ℕ → ℂ} {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hb : ∀ k : ℕ, ‖c k‖ * R ^ k ≤ C) {z : ℂ} (hz : ‖z‖ < R) :
    Summable (fun k : ℕ => c k * z ^ k) := by
  have hCnn : 0 ≤ C := le_of_lt hC
  have hratio : ‖z‖ / R < 1 := (div_lt_one hR).mpr hz
  have hnn : 0 ≤ ‖z‖ / R := by positivity
  -- The dominating geometric series `C * (‖z‖ / R) ^ k` is summable.
  have hsum : Summable (fun k : ℕ => C * (‖z‖ / R) ^ k) :=
    (summable_geometric_of_lt_one hnn hratio).mul_left C
  -- Termwise domination.
  have hbound : ∀ k : ℕ, ‖c k * z ^ k‖ ≤ C * (‖z‖ / R) ^ k := by
    intro k
    have hRk : 0 < R ^ k := pow_pos hR k
    have hle : ‖c k‖ ≤ C / R ^ k := by
      rw [le_div_iff₀ hRk]; exact hb k
    rw [norm_mul, norm_pow]
    calc ‖c k‖ * ‖z‖ ^ k ≤ (C / R ^ k) * ‖z‖ ^ k :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = C * (‖z‖ / R) ^ k := by rw [div_pow]; ring
  exact Summable.of_norm_bounded hsum hbound

end Work.C17I
