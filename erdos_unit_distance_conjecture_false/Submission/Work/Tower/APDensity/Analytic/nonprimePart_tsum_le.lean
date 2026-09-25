import Mathlib
import Submission.Work.Tower.APDensity.Basic

/-!
# The prime-power (non-prime) part of the Dirichlet series of `LambdaOne` at exponent `1`

For the residue-class von Mangoldt function `LambdaOne` (the von Mangoldt function restricted to
the class `1 mod 3`), the part of the Dirichlet series supported on the *non-prime* numbers is
summable at the exponent `1`. This is the classical fact that the contribution of the prime powers
`p ^ k`, `k ≥ 2`, to `∑ Λ(n)/n` converges (each prime `p` contributes at most `2 log p / p ^ 2`).

We record the summability and deduce that the whole series at exponent `1 + δ`, `δ ≥ 0`, is
dominated termwise by the series at exponent `1`, hence its `tsum` is bounded by the `tsum` at
exponent `1`.
-/

namespace Work.Tower.APDensity.Analytic

/-- The series `∑_{n non-prime} Λ₁(n) / n` converges: `LambdaOne` is the von Mangoldt function
restricted to the class `1 mod 3`, and this is the classical summability of the sum over the prime
powers `p ^ k`, `k ≥ 2` (Mathlib: `summable_residueClass_non_primes_div`). -/
lemma summable_nonprimePart_div :
    Summable fun n : ℕ => (if n.Prime then 0 else Work.Tower.LambdaOne n) / (n : ℝ) :=
  ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (1 : ZMod 3)

theorem nonprimePart_tsum_le {δ : ℝ} (hδ : 0 ≤ δ) :
    ∑' n : ℕ, (if n.Prime then 0 else Work.Tower.LambdaOne n) / (n : ℝ) ^ (1 + δ)
      ≤ ∑' n : ℕ, (if n.Prime then 0 else Work.Tower.LambdaOne n) / (n : ℝ) := by
  have hsumm1 := summable_nonprimePart_div
  have hnum : ∀ n : ℕ, 0 ≤ (if n.Prime then 0 else Work.Tower.LambdaOne n) := by
    intro n
    split_ifs with h
    · exact le_rfl
    · exact Work.Tower.lambdaOne_nonneg n
  have hnn : ∀ n : ℕ,
      0 ≤ (if n.Prime then 0 else Work.Tower.LambdaOne n) / (n : ℝ) ^ (1 + δ) := by
    intro n
    exact div_nonneg (hnum n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hle : ∀ n : ℕ, (if n.Prime then 0 else Work.Tower.LambdaOne n) / (n : ℝ) ^ (1 + δ)
      ≤ (if n.Prime then 0 else Work.Tower.LambdaOne n) / (n : ℝ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow (by linarith : (1 : ℝ) + δ ≠ 0)]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hpow : (n : ℝ) ^ (1 : ℝ) ≤ (n : ℝ) ^ (1 + δ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      rw [Real.rpow_one] at hpow
      exact div_le_div_of_nonneg_left (hnum n) hnpos hpow
  exact Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le hnn hle hsumm1) hsumm1

end Work.Tower.APDensity.Analytic
