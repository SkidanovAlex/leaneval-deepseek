import Mathlib
import Submission.Commons.NumberTheory.Lagarias.finite_check_range_1_500
import Submission.Commons.NumberTheory.Lagarias.finite_check_range_501_1000
import Submission.Commons.NumberTheory.Lagarias.finite_check_range_1001_1500
import Submission.Commons.NumberTheory.Lagarias.finite_check_range_1501_2000
import Submission.Commons.NumberTheory.Lagarias.finite_check_range_2001_2500
import Submission.Commons.NumberTheory.Lagarias.finite_check_range_2501_3000
import Submission.Commons.NumberTheory.Lagarias.finite_check_range_3001_3500
import Submission.Commons.NumberTheory.Lagarias.finite_check_range_3501_4000
import Submission.Commons.NumberTheory.Lagarias.finite_check_range_4001_4500
import Submission.Commons.NumberTheory.Lagarias.finite_check_range_4501_5000
import Submission.Commons.NumberTheory.Lagarias.finite_check_range_5001_5040

open scoped ArithmeticFunction.sigma

namespace Commons.NumberTheory.Lagarias

theorem finite_check (n : ℕ) (hn0 : 0 < n) (hn : n ≤ 5040) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  by_cases h1 : n ≤ 500
  · exact finite_check_range_1_500 n hn0 (by omega) h1
  · have h501 : 501 ≤ n := by omega
    by_cases h501 : n ≤ 1000
    · exact finite_check_range_501_1000 n hn0 (by omega) h501
    · have h1001 : 1001 ≤ n := by omega
      by_cases h1001 : n ≤ 1500
      · exact finite_check_range_1001_1500 n hn0 (by omega) h1001
      · have h1501 : 1501 ≤ n := by omega
        by_cases h1501 : n ≤ 2000
        · exact finite_check_range_1501_2000 n hn0 (by omega) h1501
        · have h2001 : 2001 ≤ n := by omega
          by_cases h2001 : n ≤ 2500
          · exact finite_check_range_2001_2500 n hn0 (by omega) h2001
          · have h2501 : 2501 ≤ n := by omega
            by_cases h2501 : n ≤ 3000
            · exact finite_check_range_2501_3000 n hn0 (by omega) h2501
            · have h3001 : 3001 ≤ n := by omega
              by_cases h3001 : n ≤ 3500
              · exact finite_check_range_3001_3500 n hn0 (by omega) h3001
              · have h3501 : 3501 ≤ n := by omega
                by_cases h3501 : n ≤ 4000
                · exact finite_check_range_3501_4000 n hn0 (by omega) h3501
                · have h4001 : 4001 ≤ n := by omega
                  by_cases h4001 : n ≤ 4500
                  · exact finite_check_range_4001_4500 n hn0 (by omega) h4001
                  · have h4501 : 4501 ≤ n := by omega
                    by_cases h4501 : n ≤ 5000
                    · exact finite_check_range_4501_5000 n hn0 (by omega) h4501
                    · have h5001 : 5001 ≤ n := by omega
                      exact finite_check_range_5001_5040 n hn0 (by omega) hn

end Commons.NumberTheory.Lagarias
