import Mathlib
import ChallengeDeps
import Submission.LargeCase
import Submission.SmallN
import Submission.QCover

/-! Final assembly of Theorem 1.1 (flat Littlewood polynomials exist):

  δ := min (2^(-174)) δs ,   Δ := N0 + 1

where `N0 = 2^402`; `Large.large_case` covers `n ≥ N0` (lower `2^(-174)·√n`,
upper `2^15·√n ≤ Δ√n`), `Small.small_case N0` covers `2 ≤ n < N0` (lower
`δs·√n ≥ δ√n`, upper `(N0+1)√n = Δ√n`).  `Δ > δ`, `δ > 0` are immediate. -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

open FlatLittlewoodPoly

namespace Submission

/-- Final theorem, matching `Submission.theorem_1_1`. -/
theorem theorem_1_1_final :
    ∃ Δ δ : ℝ, Δ > δ ∧ δ > 0 ∧ ∀ n ≥ 2,
      ∃ P : ℂ[X], IsLittlewoodPolynomial P ∧ P.natDegree = n ∧
      ∀ z : ℂ, ‖z‖ = 1 → δ * √n ≤ ‖P.eval z‖ ∧
      ‖P.eval z‖ ≤ Δ * √n := by
  classical
  have h2N : 2 ≤ Large.N0 := by
    unfold Large.N0
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by norm_num : 1 ≤ 402))
  obtain ⟨δs, hδs0, hsmall⟩ := Small.small_case Large.N0 h2N
  let δ : ℝ := min ((2 : ℝ) ^ 174)⁻¹ δs
  let Δ : ℝ := (Large.N0 : ℝ) + 1
  refine ⟨Δ, δ, ?hΔδ, ?hδ0, ?hall⟩
  · -- Δ > δ
    have h1 : δ ≤ ((2 : ℝ) ^ 174)⁻¹ := min_le_left _ _
    have h2 : ((2 : ℝ) ^ 174)⁻¹ < 1 := by
      have hgt : 1 < (2 : ℝ) ^ 174 := by
        simpa using (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (by norm_num : 0 < 174))
      exact inv_lt_one_of_one_lt₀ hgt
    have h3 : 1 ≤ Δ := by
      unfold Δ
      exact le_add_of_nonneg_left (by positivity : (0 : ℝ) ≤ (Large.N0 : ℝ))
    linarith
  · -- δ > 0
    exact lt_min (by positivity : 0 < ((2 : ℝ) ^ 174)⁻¹) hδs0
  · -- ∀ n ≥ 2
    intro n hn2
    by_cases hn : Large.N0 ≤ n
    · -- large case
      rcases Large.large_case n hn with ⟨P, hP, hdeg, hb⟩
      refine ⟨P, hP, hdeg, ?_⟩
      intro z hz
      have hlo := (hb z hz).1
      have hhi := (hb z hz).2
      constructor
      · have hmul : δ * Real.sqrt (n : ℝ) ≤ ((2 : ℝ) ^ 174)⁻¹ * Real.sqrt (n : ℝ) := by
          exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
        exact le_trans hmul hlo
      · have h15 : (2 ^ 15 : ℝ) ≤ Δ := by
          have hN : (2 ^ 15 : ℕ) ≤ Large.N0 := by
            unfold Large.N0
            exact pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by norm_num : 15 ≤ 402)
          have hc : (2 ^ 15 : ℝ) ≤ (Large.N0 : ℝ) := by exact_mod_cast hN
          unfold Δ
          linarith
        have hmul : (2 ^ 15 : ℝ) * Real.sqrt (n : ℝ) ≤ Δ * Real.sqrt (n : ℝ) := by
          exact mul_le_mul_of_nonneg_right h15 (Real.sqrt_nonneg _)
        exact le_trans hhi hmul
    · -- small case
      have hnlt : n < Large.N0 := lt_of_not_ge hn
      rcases hsmall n hn2 hnlt with ⟨P, hP, hdeg, hb⟩
      refine ⟨P, hP, hdeg, ?_⟩
      intro z hz
      have hlo := (hb z hz).1
      have hhi := (hb z hz).2
      constructor
      · have hmul : δ * Real.sqrt (n : ℝ) ≤ δs * Real.sqrt (n : ℝ) := by
          exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
        exact le_trans hmul hlo
      · simpa [Δ] using hhi
end Submission
