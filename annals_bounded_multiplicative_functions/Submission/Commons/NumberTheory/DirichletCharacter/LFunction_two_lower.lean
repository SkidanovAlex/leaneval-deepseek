import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ZetaValues

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter
open scoped BigOperators LSeries.notation ArithmeticFunction.Moebius

namespace Commons.NumberTheory.DirichletCharacter

/-- A Dirichlet series on the line `Re s = 2` whose coefficients are bounded by `1` is
bounded by `∑ n⁻² = π²/6 ≤ 2`. -/
private lemma norm_LSeries_le_two_of_norm_le_one {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (T : ℝ) :
    ‖LSeries f ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ 2 := by
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hsre : s.re = 2 := by simp [s]
  have hF_le_G : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤ ((n : ℝ) ^ 2)⁻¹ := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      simp
    · rw [LSeries.norm_term_eq, if_neg (by omega : n ≠ 0)]
      calc ‖f n‖ / (n : ℝ) ^ s.re = ‖f n‖ / (n : ℝ) ^ 2 := by rw [hsre]; norm_num
        _ ≤ 1 / (n : ℝ) ^ 2 := div_le_div_of_nonneg_right (hf n) (sq_nonneg _)
        _ = ((n : ℝ) ^ 2)⁻¹ := by rw [one_div]
  have hG_summ : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
    simpa only [one_div] using hasSum_zeta_two.summable
  have hF_summ : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hF_le_G hG_summ
  have htsum_le : (∑' n : ℕ, ‖LSeries.term f s n‖) ≤ ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ :=
    Summable.tsum_le_tsum hF_le_G hF_summ hG_summ
  have hzeta : (∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) ≤ 2 := by
    have heq : (∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) = Real.pi ^ 2 / 6 := by
      simpa [one_div] using hasSum_zeta_two.tsum_eq
    have hpi : Real.pi ^ 2 / 6 ≤ 2 := by
      nlinarith [Real.pi_pos, Real.pi_lt_d2]
    rw [heq]; exact hpi
  have hnorm : ‖LSeries f s‖ ≤ 2 := by
    have h1 : ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ :=
      norm_tsum_le_tsum_norm hF_summ
    linarith
  simpa [s] using hnorm

/-- On the line `Re s = 2`, the L-function of any Dirichlet character is bounded away
from zero by `1/2`. -/
theorem LFunction_two_lower {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) :
    (1 / 2 : ℝ) ≤ ‖DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (T : ℂ))‖ := by
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hs : 1 < s.re := by simp [s]
  let f : ℕ → ℂ := fun n => (χ (n : ZMod N) : ℂ)
  let h : ℕ → ℂ := fun n => f n * (ArithmeticFunction.moebius n : ℂ)
  have hmul : LSeries f s * LSeries h s = 1 := by
    have h0 := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
    have hfun : ((fun n : ℕ => (χ (n : ZMod N) : ℂ)) * fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
        = (fun n : ℕ => (χ (n : ZMod N) : ℂ) * (ArithmeticFunction.moebius n : ℂ)) := by
      funext n; rw [Pi.mul_apply]
    rw [hfun] at h0
    simpa [f, h] using h0
  have hhn : ∀ n : ℕ, ‖h n‖ ≤ 1 := by
    intro n
    simp only [h]
    rw [norm_mul]
    exact mul_le_one₀ (χ.norm_le_one (n : ZMod N)) (norm_nonneg _) (by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n))
  have hbnd : ‖LSeries h s‖ ≤ 2 := by
    simpa [s] using norm_LSeries_le_two_of_norm_le_one (f := h) hhn T
  have hprod : ‖LSeries f s‖ * ‖LSeries h s‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have key : (1 : ℝ) ≤ ‖LSeries f s‖ * 2 := by
    calc (1 : ℝ) = ‖LSeries f s‖ * ‖LSeries h s‖ := hprod.symm
      _ ≤ ‖LSeries f s‖ * 2 := mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)
  have hmain : (1 / 2 : ℝ) ≤ ‖LSeries f s‖ := by linarith
  have hLF : DirichletCharacter.LFunction χ s = LSeries f s := by
    simpa [f] using DirichletCharacter.LFunction_eq_LSeries χ hs
  have hnorm_eq : ‖DirichletCharacter.LFunction χ s‖ = ‖LSeries f s‖ := by rw [hLF]
  change (1 / 2 : ℝ) ≤ ‖DirichletCharacter.LFunction χ s‖
  rw [hnorm_eq]
  exact hmain

end Commons.NumberTheory.DirichletCharacter