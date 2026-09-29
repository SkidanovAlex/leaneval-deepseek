import Mathlib

namespace Work.TMComp.MAnalytic

/-- If `‖a m n‖ * r^(m+n) ≤ M` and `‖z‖ < r`, `‖w‖ < r`, then the double series
`∑_{m,n} a m n z^m w^n` is (unconditionally) summable. -/
theorem summable_double_of_bound {a : ℕ → ℕ → ℂ} {z w : ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hb : ∀ m n : ℕ, ‖a m n‖ * r ^ (m + n) ≤ M) (hz : ‖z‖ < r) (hw : ‖w‖ < r) :
    Summable (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) := by
  set ρz : ℝ := ‖z‖ / r with hρz
  set ρw : ℝ := ‖w‖ / r with hρw
  have hrρz : r * ρz = ‖z‖ := by rw [hρz]; field_simp
  have hrρw : r * ρw = ‖w‖ := by rw [hρw]; field_simp
  have hρz_nonneg : 0 ≤ ρz := by rw [hρz]; positivity
  have hρw_nonneg : 0 ≤ ρw := by rw [hρw]; positivity
  have hρz_lt : ρz < 1 := by rw [hρz]; rw [div_lt_one hr]; exact hz
  have hρw_lt : ρw < 1 := by rw [hρw]; rw [div_lt_one hr]; exact hw
  have hmul : Summable (fun p : ℕ × ℕ => ρz ^ p.1 * ρw ^ p.2) :=
    Summable.mul_of_nonneg (summable_geometric_of_lt_one hρz_nonneg hρz_lt)
      (summable_geometric_of_lt_one hρw_nonneg hρw_lt)
      (fun m => pow_nonneg hρz_nonneg m) (fun n => pow_nonneg hρw_nonneg n)
  have hmaj : Summable (fun p : ℕ × ℕ => M * ρz ^ p.1 * ρw ^ p.2) := by
    have := hmul.mul_left M
    simpa only [mul_assoc] using this
  refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ => M * ρz ^ p.1 * ρw ^ p.2) hmaj ?_
  rintro ⟨m, n⟩
  have h1 : ‖a m n * z ^ m * w ^ n‖ = ‖a m n‖ * ‖z‖ ^ m * ‖w‖ ^ n := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
  have h2 : ‖a m n‖ * ‖z‖ ^ m * ‖w‖ ^ n = (‖a m n‖ * r ^ (m + n)) * (ρz ^ m * ρw ^ n) := by
    rw [← hrρz, ← hrρw, mul_pow, mul_pow, pow_add]; ring
  have h3 : (‖a m n‖ * r ^ (m + n)) * (ρz ^ m * ρw ^ n) ≤ M * ρz ^ m * ρw ^ n := by
    have hc : 0 ≤ ρz ^ m * ρw ^ n :=
      mul_nonneg (pow_nonneg hρz_nonneg m) (pow_nonneg hρw_nonneg n)
    have hle := mul_le_mul_of_nonneg_right (hb m n) hc
    simpa only [mul_assoc] using hle
  calc ‖a m n * z ^ m * w ^ n‖ = ‖a m n‖ * ‖z‖ ^ m * ‖w‖ ^ n := h1
    _ = (‖a m n‖ * r ^ (m + n)) * (ρz ^ m * ρw ^ n) := h2
    _ ≤ M * ρz ^ m * ρw ^ n := h3

end Work.TMComp.MAnalytic
