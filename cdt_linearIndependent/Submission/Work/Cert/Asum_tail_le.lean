import Mathlib
import Submission.Work.Cert.ThetaDefs

namespace Work.Cert

/-- The exponents occurring in the tail `∑ₙ q^{tri (n+13)}` start at `91 = tri 13` and grow by at
least `14` at each step: `tri (n+13) ≥ 91 + 14n`. -/
lemma tri_add_thirteen_ge (n : ℕ) : 91 + 14 * n ≤ tri (n + 13) := by
  induction n with
  | zero => norm_num [tri]
  | succ n ih =>
    rw [show n + 1 + 13 = (n + 13) + 1 by omega, tri_succ]
    omega

/-- Tail bound for the triangular theta series: if `‖q‖ ≤ ρ` with `0 ≤ ρ < 1`, then
`‖∑ₙ q^{tri (n+13)}‖ ≤ ρ^{91}/(1-ρ)`. -/
theorem Asum_tail_le {q : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hq : ‖q‖ ≤ ρ) :
    ‖∑' n : ℕ, q ^ tri (n + 13)‖ ≤ ρ ^ 91 / (1 - ρ) := by
  have hρle1 : ρ ≤ 1 := le_of_lt hρ1
  have hρ14nn : 0 ≤ ρ ^ 14 := pow_nonneg hρ0 14
  have hρ14lt : ρ ^ 14 < 1 := pow_lt_one₀ hρ0 hρ1 (by norm_num)
  have hρ14le : ρ ^ 14 ≤ ρ := by
    simpa using pow_le_pow_of_le_one hρ0 hρle1 (by norm_num : 1 ≤ 14)
  have hsumm_g : Summable (fun n : ℕ => ρ ^ 91 * (ρ ^ 14) ^ n) :=
    (summable_geometric_of_lt_one hρ14nn hρ14lt).mul_left _
  have hbound : ∀ n : ℕ, ‖q ^ tri (n + 13)‖ ≤ ρ ^ 91 * (ρ ^ 14) ^ n := by
    intro n
    have h1 : ‖q ^ tri (n + 13)‖ = ‖q‖ ^ tri (n + 13) := norm_pow _ _
    rw [h1]
    calc ‖q‖ ^ tri (n + 13) ≤ ρ ^ tri (n + 13) := pow_le_pow_left₀ (norm_nonneg q) hq _
      _ ≤ ρ ^ (91 + 14 * n) := pow_le_pow_of_le_one hρ0 hρle1 (tri_add_thirteen_ge n)
      _ = ρ ^ 91 * (ρ ^ 14) ^ n := by rw [pow_add, pow_mul]
  have hsumm_a : Summable (fun n : ℕ => ‖q ^ tri (n + 13)‖) :=
    Summable.of_nonneg_of_le (fun n => by positivity) (fun n => hbound n) hsumm_g
  have hle2 : ∑' n : ℕ, ‖q ^ tri (n + 13)‖ ≤ ∑' n : ℕ, ρ ^ 91 * (ρ ^ 14) ^ n :=
    Summable.tsum_le_tsum hbound hsumm_a hsumm_g
  have hgts : ∑' n : ℕ, ρ ^ 91 * (ρ ^ 14) ^ n = ρ ^ 91 * (1 - ρ ^ 14)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hρ14nn hρ14lt]
  calc ‖∑' n : ℕ, q ^ tri (n + 13)‖ ≤ ∑' n : ℕ, ‖q ^ tri (n + 13)‖ :=
        norm_tsum_le_tsum_norm hsumm_a
    _ ≤ ∑' n : ℕ, ρ ^ 91 * (ρ ^ 14) ^ n := hle2
    _ = ρ ^ 91 * (1 - ρ ^ 14)⁻¹ := hgts
    _ ≤ ρ ^ 91 * (1 - ρ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hρ0 91)
        exact (inv_le_inv₀ (by linarith) (by linarith)).mpr (by linarith)
    _ = ρ ^ 91 / (1 - ρ) := by rw [div_eq_mul_inv]

end Work.Cert
