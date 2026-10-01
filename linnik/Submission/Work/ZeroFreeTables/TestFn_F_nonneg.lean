/-
# ZeroFreeTables — TestFn_F_nonneg

Non-negativity of the real-axis Laplace transform `F` of a test function satisfying
HB's Conditions 1 and 2: `F` is the Laplace transform of the non-negative function
`f`, hence non-negative on the whole real axis.  (This is the real-axis half of
Condition 2, and it is what makes the `F`-inequalities of §6/§8/§9 have a sign.)
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral

namespace Work.ZeroFreeTables

/-- The real-axis Laplace transform of a non-negative test function is
non-negative. -/
theorem TestFn_F_nonneg (T : TestFn) : ∀ x : ℝ, 0 ≤ T.F x := by
  intro x
  rw [TestFn_F_eq_integral T x]
  exact intervalIntegral.integral_nonneg (le_of_lt T.x₀_pos)
    (fun u _ => mul_nonneg (Real.exp_pos _).le (T.f_nonneg u))

end Work.ZeroFreeTables
