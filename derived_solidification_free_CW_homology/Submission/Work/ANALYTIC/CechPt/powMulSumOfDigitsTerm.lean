import Mathlib
import Submission.Work.ANALYTIC.CechPt.CechLevels

namespace Work.ANALYTIC.CechPt

theorem powMulSumOfDigitsTerm (n : ℕ) (d : ℕ → Fin 2) :
    (2 : ℝ) ^ (n + 1) * (∑ i ∈ Finset.range (n + 1), Real.ofDigitsTerm d i)
      = (Work.ANALYTIC.CechPt.truncOf n d : ℝ) := by
  rw [Finset.mul_sum, Work.ANALYTIC.CechPt.truncOf]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ (i + 1) * (2 : ℝ) ^ (n - i) := by
    rw [← pow_add]; congr 1; omega
  rw [h]
  simp only [Real.ofDigitsTerm]
  field_simp
  ring

end Work.ANALYTIC.CechPt
