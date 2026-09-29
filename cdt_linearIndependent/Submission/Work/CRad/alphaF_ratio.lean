import Mathlib
import Submission.Work.CRad.alphaF_arith
import Submission.Work.CRad.alphaF_ratio_step

namespace Work.CRad

theorem alphaF_ratio (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hgap : 10 ^ 6 * (((m : ℤ) - (n : ℤ)).natAbs) ≤ n) :
    (((2 * n + 1 : ℕ) : ℝ) + Real.sqrt ((((2 * n + 1 : ℕ) : ℝ)) ^ 2 - 1)) ≤
        (1001 / 1000 : ℝ) * ((((2 * m + 1 : ℕ) : ℝ)) + Real.sqrt ((((2 * m + 1 : ℕ) : ℝ)) ^ 2 - 1)) ∧
      ((((2 * m + 1 : ℕ) : ℝ)) + Real.sqrt ((((2 * m + 1 : ℕ) : ℝ)) ^ 2 - 1)) ≤
        (1001 / 1000 : ℝ) * ((((2 * n + 1 : ℕ) : ℝ)) + Real.sqrt ((((2 * n + 1 : ℕ) : ℝ)) ^ 2 - 1)) := by
  by_cases hmn : m = n
  · rw [hmn]
    have hX : (0 : ℝ) ≤ (((2 * n + 1 : ℕ) : ℝ)) + Real.sqrt ((((2 * n + 1 : ℕ) : ℝ)) ^ 2 - 1) := by
      have h1 := Real.sqrt_nonneg ((((2 * n + 1 : ℕ) : ℝ)) ^ 2 - 1)
      have h2 : (0 : ℝ) ≤ (((2 * n + 1 : ℕ) : ℝ)) := by positivity
      linarith
    constructor <;> nlinarith [hX]
  · obtain ⟨h4000n999, h4000m999⟩ := alphaF_arith m n hmn hgap
    have hAcast : (((2 * n + 1 : ℕ) : ℝ)) = 2 * (n : ℝ) + 1 := by push_cast; ring
    have hBcast : (((2 * m + 1 : ℕ) : ℝ)) = 2 * (m : ℝ) + 1 := by push_cast; ring
    have hA1 : (1 : ℝ) ≤ (((2 * n + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (by omega : (1 : ℕ) ≤ 2 * n + 1)
    have hB1 : (1 : ℝ) ≤ (((2 * m + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (by omega : (1 : ℕ) ≤ 2 * m + 1)
    constructor
    · apply alphaF_ratio_step hA1 hB1
      rw [hAcast, hBcast]
      nlinarith [h4000n999]
    · apply alphaF_ratio_step hB1 hA1
      rw [hBcast, hAcast]
      nlinarith [h4000m999]

end Work.CRad
