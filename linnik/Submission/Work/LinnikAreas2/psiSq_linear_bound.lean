import Mathlib
import Submission.Work.LinnikAreas2.PsiDefs2

namespace Work.LinnikAreas2

set_option linter.unusedVariables false

/-- Pointwise (linear in `n`) bound for the `ψ`-mollifier square `Ψ(n)²`, deduced from the
cumulative bounds `h1` (on the range `U ≤ N ≤ V`) and `h2` (on `N ≥ V`) for the partial sums
`psSum U V N`.  Since `Ψ(n)² ≤ psSum U V n` and `psSum` is bounded by `((1+ε)/log(V/U) +
C₁/log(V/U)²) N` on the whole range `N ≥ U` (the logarithmic factor `log(N/U)` being largest at
`N = V`), while `Ψ(n)²` vanishes for `2 ≤ n < U`, the constant `max 1 (...) · n` holds for all
`n`. -/
theorem psiSq_linear_bound {ε C₁ U V : ℝ} (hε : 0 < ε) (hC₁ : 0 < C₁) (hU : 0 < U)
    (hUV : U < V) (hU1 : 1 ≤ U)
    (h1 : ∀ N : ℕ, U ≤ (N:ℝ) → (N:ℝ) ≤ V →
      Work.LinnikAreas2.psSum U V N
        ≤ (1+ε) * (N:ℝ) * Real.log ((N:ℝ)/U) / (Real.log (V/U))^2
          + C₁ * (N:ℝ) / (Real.log (V/U))^2)
    (h2 : ∀ N : ℕ, V ≤ (N:ℝ) →
      Work.LinnikAreas2.psSum U V N
        ≤ (1+ε) * (N:ℝ) / Real.log (V/U) + C₁ * (N:ℝ) / (Real.log (V/U))^2) :
    ∀ n : ℕ, Work.LinnikAreas2.psiSq U V n
      ≤ max 1 ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * n := by
  intro n
  have hUVle : U ≤ V := hUV.le
  have hlogpos : 0 < Real.log (V/U) := by
    apply Real.log_pos
    rw [one_lt_div hU]
    exact hUV
  set M : ℝ := max 1 ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) with hMdef
  have hMge : (1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2 ≤ M := le_max_right _ _
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: both sides vanish
    subst hn0
    have hzero : Work.LinnikAreas2.psiSq U V 0 = 0 := by
      rw [Work.LinnikAreas2.psiSq, Nat.divisors_zero, Finset.sum_empty]
      ring
    rw [hzero]
    simp
  by_cases hnU : (n:ℝ) < U
  · -- `n` below the range: `Ψ(n)² = 0` for `n ≥ 2`, and `= 1 ≤ M` for `n = 1`
    rcases lt_or_ge n 2 with hsmall | hbig
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [Work.LinnikAreas2.psiSq_one hU1, Nat.cast_one, mul_one]
      exact hM1
    · rw [Work.LinnikAreas2.psiSq_eq_zero hU1 hUVle hbig (le_of_lt hnU)]
      exact mul_nonneg hM0.le (Nat.cast_nonneg n)
  · have hUn : U ≤ (n:ℝ) := not_lt.mp hnU
    have hn1 : 1 ≤ n := by
      have h : (1:ℝ) ≤ (n:ℝ) := le_trans hU1 hUn
      exact_mod_cast h
    have hps := Work.LinnikAreas2.psiSq_le_psSum (U := U) (V := V) hn1 (le_refl n)
    rcases lt_or_ge (n:ℝ) V with hVcase | hVcase
    · -- `U ≤ n ≤ V`: the logarithmic factor is maximal at `N = V`
      have hb := h1 n hUn (le_of_lt hVcase)
      have hlog_le : Real.log ((n:ℝ)/U) ≤ Real.log (V/U) := by
        apply Real.log_le_log
        · exact div_pos (lt_of_lt_of_le hU hUn) hU
        · rw [div_le_div_iff₀ hU hU]
          exact mul_le_mul_of_nonneg_right hVcase.le hU.le
      have hA : (1+ε) * (n:ℝ) * Real.log ((n:ℝ)/U) / (Real.log (V/U))^2
            ≤ (1+ε) * (n:ℝ) / Real.log (V/U) := by
        rw [div_le_div_iff₀ (by positivity) hlogpos]
        have hc : 0 ≤ (1+ε) * (n:ℝ) * Real.log (V/U) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hlog_le hc]
      have hsum : (1+ε) * (n:ℝ) / Real.log (V/U) + C₁ * (n:ℝ) / (Real.log (V/U))^2
            = ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * (n:ℝ) := by ring
      have hmain : ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * (n:ℝ) ≤ M * (n:ℝ) :=
        mul_le_mul_of_nonneg_right hMge (Nat.cast_nonneg n)
      linarith
    · -- `n ≥ V`
      have hb := h2 n hVcase
      have hsum : (1+ε) * (n:ℝ) / Real.log (V/U) + C₁ * (n:ℝ) / (Real.log (V/U))^2
            = ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * (n:ℝ) := by ring
      have hmain : ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * (n:ℝ) ≤ M * (n:ℝ) :=
        mul_le_mul_of_nonneg_right hMge (Nat.cast_nonneg n)
      linarith

end Work.LinnikAreas2
