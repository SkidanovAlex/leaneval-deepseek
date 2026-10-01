import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs
import Submission.Work.LinnikAreas.Density4.thetaDiag_sum_bounds
import Submission.Work.LinnikAreas.Density4.sum_shift_range_le_tsum
import Submission.Work.LinnikAreas.Density4.Icc_two_sum_range
import Submission.Work.LinnikAreas.Density4.tdH_summable_shift

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

open Set MeasureTheory intervalIntegral Real

/-- The partial sums of the majorant `tdH σ A n = n^{σ-1} e^{-n/A}` are bounded by
`Γ(σ) A^σ`: they are dominated by the tail `∑' n, h(n+1)` of the majorant, which the
integral test (with the correction `h 1 + ∫_1^∞ h ≤ ∫_0^∞ h` accounting for the first
term) bounds by `Γ(σ) A^σ`. -/
theorem thetaDiag_sum_le_kappa (σ A : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : 1 ≤ A) :
    ∀ N : ℕ, (∑ n ∈ Finset.Icc 2 N, Work.LinnikAreas.Density4.tdH σ A n) ≤ Real.Gamma σ * A ^ σ := by
  have hApos : (0:ℝ) < A := lt_of_lt_of_le one_pos hA
  -- the shifted majorant is summable (integral test on `[1,∞)`)
  have hsumm : Summable (fun n : ℕ => tdH σ A (n + 1)) := tdH_summable_shift σ A hσ1 hApos
  have hnonneg : ∀ n : ℕ, 0 ≤ tdH σ A (n + 1) := by
    intro n
    simp only [tdH, Nat.cast_add, Nat.cast_one]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  -- the integral-test bound for the full tail `∑' n, h(n+1)`
  have htsum := thetaDiag_conj1 σ A hσ hσ1 hA
  intro N
  calc (∑ n ∈ Finset.Icc 2 N, Work.LinnikAreas.Density4.tdH σ A n)
      = ∑ k ∈ Finset.range (N - 1), tdH σ A (k + 2) := Icc_two_sum_range (tdH σ A) N
    _ = ∑ k ∈ Finset.range (N - 1), (fun n : ℕ => tdH σ A (n + 1)) (k + 1) := by
        apply Finset.sum_congr rfl; intro k hk; congr 1
    _ ≤ ∑' n : ℕ, (fun n : ℕ => tdH σ A (n + 1)) n :=
        sum_shift_range_le_tsum (fun n : ℕ => tdH σ A (n + 1)) hsumm hnonneg (N - 1)
    _ = ∑' n : ℕ, ((n:ℝ)+1)^(σ-1) * Real.exp (-((n:ℝ)+1)/A) := by
        apply tsum_congr; intro n; simp only [tdH, Nat.cast_add, Nat.cast_one]
    _ ≤ Real.Gamma σ * A ^ σ := htsum

end Work.LinnikAreas.Density4
