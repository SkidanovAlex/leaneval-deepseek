import Mathlib
import Submission.Work.Cert.ThetaDefs

namespace Work.Cert

theorem Bsum_tail_le {q : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hq : ‖q‖ ≤ ρ) :
    ‖∑' n : ℕ, (2 * (-1 : ℂ) ^ (n + 13) * q ^ ((n + 13) ^ 2))‖ ≤ 2 * ρ ^ 169 / (1 - ρ) := by
  -- The dominating geometric series `∑ 2·ρ^169·ρ^n`.
  have hsumg : Summable (fun n : ℕ => 2 * ρ ^ 169 * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  -- Termwise norm bound: the `n`-th term is dominated by `2·ρ^169·ρ^n`.
  have hb : ∀ n : ℕ, ‖2 * (-1 : ℂ) ^ (n + 13) * q ^ ((n + 13) ^ 2)‖ ≤ 2 * ρ ^ 169 * ρ ^ n := by
    intro n
    have hnorm : ‖2 * (-1 : ℂ) ^ (n + 13) * q ^ ((n + 13) ^ 2)‖ = 2 * ‖q‖ ^ ((n + 13) ^ 2) := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow]
      simp
    rw [hnorm]
    -- `(n+13)^2 = 169 + n + (n^2 + 25n)`, and `ρ`-powers are decreasing in the exponent.
    have he : (n + 13) ^ 2 = (169 + n) + (n ^ 2 + 25 * n) := by ring
    have hpow : ρ ^ ((n + 13) ^ 2) ≤ ρ ^ 169 * ρ ^ n := by
      calc ρ ^ ((n + 13) ^ 2) = ρ ^ (169 + n) * ρ ^ (n ^ 2 + 25 * n) := by rw [he, pow_add]
        _ ≤ ρ ^ (169 + n) * 1 := by
              gcongr
              exact pow_le_one₀ hρ0 (le_of_lt hρ1)
        _ = ρ ^ 169 * ρ ^ n := by rw [pow_add]; ring
    calc 2 * ‖q‖ ^ ((n + 13) ^ 2) ≤ 2 * ρ ^ ((n + 13) ^ 2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg q) hq _) (by norm_num)
      _ ≤ 2 * ρ ^ 169 * ρ ^ n := by linarith [hpow]
  have hsuma_norm : Summable (fun n : ℕ => ‖2 * (-1 : ℂ) ^ (n + 13) * q ^ ((n + 13) ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb hsumg
  calc ‖∑' n : ℕ, (2 * (-1 : ℂ) ^ (n + 13) * q ^ ((n + 13) ^ 2))‖
      ≤ ∑' n : ℕ, ‖2 * (-1 : ℂ) ^ (n + 13) * q ^ ((n + 13) ^ 2)‖ :=
        norm_tsum_le_tsum_norm hsuma_norm
    _ ≤ ∑' n : ℕ, 2 * ρ ^ 169 * ρ ^ n := Summable.tsum_le_tsum hb hsuma_norm hsumg
    _ = 2 * ρ ^ 169 * (1 - ρ)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ = 2 * ρ ^ 169 / (1 - ρ) := by rw [div_eq_mul_inv]

end Work.Cert
