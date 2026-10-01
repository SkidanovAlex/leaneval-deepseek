import Mathlib
import Submission.Work.LinnikAreas.Density4.Udecay.mellin_defs

namespace Work.LinnikAreas.Density4.Udecay

/-- The partial Möbius reciprocal sum `muRecipSum M = Σ_{1 ≤ n ≤ M} μ(n)/n` agrees with the sum
over `range (M+1)`, the extra `n = 0` term being `μ(0)/0 = 0`. -/
theorem muRecipSum_eq_sum_range (M : ℕ) :
    Commons.NumberTheory.Moebius.muRecipSum M
      = ∑ n ∈ Finset.range (M + 1), (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) := by
  have hrange : Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  unfold Commons.NumberTheory.Moebius.muRecipSum
  rw [hrange, Finset.sum_insert]
  · simp
  · simp [Finset.mem_Icc]

end Work.LinnikAreas.Density4.Udecay
