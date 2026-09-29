import Mathlib

namespace Work.Cert

/-- Telescoping (Lipschitz) bound for `x ↦ x ^ (n+1)` on the closed ball of radius `ρ`,
in the shifted form used by the induction: the exponent `n` on the right matches the
number of steps. -/
lemma pow_sub_le_aux {z w : ℂ} {ρ r : ℝ} (hρ : 0 ≤ ρ) (hz : ‖z‖ ≤ ρ) (hw : ‖w‖ ≤ ρ)
    (hd : ‖w - z‖ ≤ r) (n : ℕ) : ‖w ^ (n + 1) - z ^ (n + 1)‖ ≤ ((n + 1 : ℕ) : ℝ) * ρ ^ n * r := by
  induction n with
  | zero => simpa using hd
  | succ k ih =>
    have key : w ^ (k + 1 + 1) - z ^ (k + 1 + 1)
        = w ^ (k + 1) * (w - z) + (w ^ (k + 1) - z ^ (k + 1)) * z := by ring
    have hn : ‖w ^ (k + 1)‖ ≤ ρ ^ (k + 1) := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg w) hw (k + 1)
    calc ‖w ^ (k + 1 + 1) - z ^ (k + 1 + 1)‖
        = ‖w ^ (k + 1) * (w - z) + (w ^ (k + 1) - z ^ (k + 1)) * z‖ := by rw [key]
      _ ≤ ‖w ^ (k + 1) * (w - z)‖ + ‖(w ^ (k + 1) - z ^ (k + 1)) * z‖ := norm_add_le _ _
      _ = ‖w ^ (k + 1)‖ * ‖w - z‖ + ‖w ^ (k + 1) - z ^ (k + 1)‖ * ‖z‖ := by
            rw [norm_mul, norm_mul]
      _ ≤ ρ ^ (k + 1) * r + (((k + 1 : ℕ) : ℝ) * ρ ^ k * r) * ρ := by
            apply add_le_add
            · calc ‖w ^ (k + 1)‖ * ‖w - z‖ ≤ ‖w ^ (k + 1)‖ * r :=
                    mul_le_mul_of_nonneg_left hd (norm_nonneg _)
                _ ≤ ρ ^ (k + 1) * r :=
                    mul_le_mul_of_nonneg_right hn (le_trans (norm_nonneg _) hd)
            · calc ‖w ^ (k + 1) - z ^ (k + 1)‖ * ‖z‖
                    ≤ ‖w ^ (k + 1) - z ^ (k + 1)‖ * ρ :=
                        mul_le_mul_of_nonneg_left hz (norm_nonneg _)
                _ ≤ (((k + 1 : ℕ) : ℝ) * ρ ^ k * r) * ρ :=
                        mul_le_mul_of_nonneg_right ih hρ
      _ = ((k + 1 + 1 : ℕ) : ℝ) * ρ ^ (k + 1) * r := by
            rw [pow_succ]; push_cast; ring

theorem pow_sub_le {z w : ℂ} {ρ r : ℝ} (hρ : 0 ≤ ρ) (hz : ‖z‖ ≤ ρ) (hw : ‖w‖ ≤ ρ)
    (hd : ‖w - z‖ ≤ r) (T : ℕ) : ‖w ^ T - z ^ T‖ ≤ (T : ℝ) * ρ ^ (T - 1) * r := by
  match T with
  | 0 => simp
  | (n + 1) => simpa [Nat.add_sub_cancel] using pow_sub_le_aux hρ hz hw hd n

end Work.Cert
