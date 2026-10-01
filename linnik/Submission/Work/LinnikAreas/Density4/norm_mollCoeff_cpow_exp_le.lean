/-
# Area 4 — pointwise norm bound for the smoothed summand `Ψ(n)Θ(n)χ(n)·n^{-ρ}·e^{-n/X}`

For `n ≥ 1` the three factors are estimated separately:
* `‖mollCoeff q U V W χ n‖ ≤ B * n` is the hypothesis `hbound`;
* `‖n^{-ρ}‖ = n^{-Re ρ} ≤ 1` because `n ≥ 1` and `Re ρ ≥ 0`
  (`Complex.norm_cpow_eq_rpow_re_of_pos`, `Real.rpow_le_one_of_one_le_of_nonpos`);
* `‖e^{-n/X}‖ = e^{-n/X} = (e^{-1/X})^n` (`Real.exp_nat_mul`),
  which is exactly the right-hand side factor.

At `n = 0` the coefficient vanishes (`mollCoeff_zero`), so both sides are `0`.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup

open DirichletCharacter Complex

namespace Work.LinnikAreas.Density4

set_option linter.unusedVariables false

/-- Pointwise bound for the `n`-th summand of `Ssm = Σ_n Ψ(n)Θ(n)χ(n)·n^{-ρ}·e^{-n/X}`:
`‖n^{-ρ}‖ ≤ 1` for `Re ρ ≥ 0` absorbs the archimedean weight, and `e^{-n/X} = (e^{-1/X})^n`. -/
theorem norm_mollCoeff_cpow_exp_le (q : ℕ) [NeZero q] {U V W X : ℝ} (hU : 0 < U) (hX : 1 ≤ X)
    (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hβ : 0 ≤ ρ.re) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ n : ℕ, ‖mollCoeff q U V W χ n‖ ≤ B * (n : ℝ)) (n : ℕ) :
    ‖mollCoeff q U V W χ n * (n : ℂ) ^ (-ρ) * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ)‖
      ≤ B * (n : ℝ) * Real.exp (-(1 / X)) ^ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [mollCoeff, psiS_zero]
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  -- the `n^{-ρ}` factor has norm `n^{-Re ρ}`
  have hcpow : ‖(n : ℂ) ^ (-ρ)‖ = (n:ℝ) ^ (-ρ.re) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
  -- the archimedean factor is a positive real number
  have hexpnorm : ‖(((Real.exp (-(n:ℝ)/X)) : ℝ) : ℂ)‖ = Real.exp (-(n:ℝ)/X) := by
    rw [Complex.ofReal_exp, Complex.norm_exp, Complex.ofReal_re]
  rw [norm_mul, norm_mul, hcpow, hexpnorm]
  have hp1 : (n:ℝ)^(-ρ.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr hβ)
  have hp0 : 0 ≤ (n:ℝ)^(-ρ.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have he0 : 0 ≤ Real.exp (-(n:ℝ)/X) := (Real.exp_pos _).le
  have hb : 0 ≤ B * (n:ℝ) := le_trans (norm_nonneg _) (hbound n)
  -- `e^{-n/X} = (e^{-1/X})^n`
  have heq : Real.exp (-(n:ℝ)/X) = Real.exp (-(1/X))^n := by
    rw [show -(n:ℝ)/X = (n:ℝ) * (-(1/X)) by ring, Real.exp_nat_mul]
  calc ‖mollCoeff q U V W χ n‖ * (n:ℝ)^(-ρ.re) * Real.exp (-(n:ℝ)/X)
      ≤ (B * (n:ℝ)) * 1 * Real.exp (-(n:ℝ)/X) := by
        apply mul_le_mul_of_nonneg_right _ he0
        exact mul_le_mul (hbound n) hp1 hp0 hb
    _ = B * (n:ℝ) * Real.exp (-(1/X))^n := by rw [heq]; ring

end Work.LinnikAreas.Density4
