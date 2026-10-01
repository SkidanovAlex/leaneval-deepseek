import Mathlib

namespace Work.ZeroDensity.Ingham

/-- Pure arithmetic: for `N ≥ 2` and `C₂ ≥ 0`, with `P = log(2N)`,
`N·C₁·P⁴ + (1 + log N)·C₂·N·P³ ≤ (C₁ + 3C₂)·N·P⁴`.  Uses `1 + log N ≤ 3 log(2N)`. -/
theorem upperTermOneArith (C1 C2 : ℝ) (hC2 : 0 ≤ C2) (N : ℕ) (hN : 2 ≤ N) :
    (N : ℝ) * (C1 * (Real.log (2 * (N : ℝ)))^4)
      + (1 + Real.log (N : ℝ)) * (C2 * (N : ℝ) * (Real.log (2 * (N : ℝ)))^3)
    ≤ (C1 + 3 * C2) * (N : ℝ) * (Real.log (2 * (N : ℝ)))^4 := by
  set P : ℝ := Real.log (2 * (N : ℝ)) with hP
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog2le : Real.log 2 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) hN2
  have hPval : P = Real.log 2 + Real.log (N : ℝ) := by
    rw [hP, Real.log_mul (by norm_num) (ne_of_gt hNpos)]
  have hPpos : 0 < P := by rw [hPval]; linarith [Real.log_two_gt_d9]
  have hkey : 1 + Real.log (N : ℝ) ≤ 3 * P := by
    rw [hPval]
    nlinarith [Real.log_two_gt_d9, hlog2le]
  have hfac : (C1 + 3 * C2) * (N : ℝ) * P^4
        - ((N : ℝ) * (C1 * P^4) + (1 + Real.log (N : ℝ)) * (C2 * (N : ℝ) * P^3))
      = C2 * (N : ℝ) * P^3 * (3 * P - (1 + Real.log (N : ℝ))) := by
    ring
  have hnonneg : 0 ≤ C2 * (N : ℝ) * P^3 * (3 * P - (1 + Real.log (N : ℝ))) := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg hC2 (le_of_lt hNpos)
      · exact pow_nonneg (le_of_lt hPpos) 3
    · linarith
  linarith [hfac, hnonneg]

end Work.ZeroDensity.Ingham
