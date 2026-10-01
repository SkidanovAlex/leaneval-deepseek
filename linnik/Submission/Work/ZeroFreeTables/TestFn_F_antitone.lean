/-
# ZeroFreeTables — TestFn_F_antitone

Monotonicity of the real-axis Laplace transform `F` of a test function satisfying
HB's Conditions 1 and 2: `F` is the Laplace transform of a non-negative function,
hence *decreasing*.  This is the monotonicity that lets the `F`-inequalities of
§6/§8/§9 (and the tables computed from them) be read at the right end of a
`λ`-interval: a larger `λⱼ` makes `F(λⱼ − λ₁)` smaller, hence the inequality harder.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral

namespace Work.ZeroFreeTables

/-- The real-axis Laplace transform of a non-negative test function is
antitone. -/
theorem TestFn_F_antitone (T : TestFn) : Antitone T.F := by
  intro a b hab
  have hcont : ∀ y : ℝ, ContinuousOn (fun t : ℝ => Real.exp (-(y * t)) * T.f t)
      (Set.Icc 0 T.x₀) := by
    intro y
    exact ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).continuousOn).mul
      (T.f_cont.mono (fun t ht => ht.1))
  have hint : ∀ y : ℝ, IntervalIntegrable (fun t : ℝ => Real.exp (-(y * t)) * T.f t)
      MeasureTheory.volume (0 : ℝ) T.x₀ :=
    fun y => ContinuousOn.intervalIntegrable_of_Icc (le_of_lt T.x₀_pos) (hcont y)
  rw [TestFn_F_eq_integral T a, TestFn_F_eq_integral T b]
  exact intervalIntegral.integral_mono_on (le_of_lt T.x₀_pos) (hint b) (hint a)
    (fun u hu => mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by
        have h := mul_le_mul_of_nonneg_right hab hu.1
        linarith))
      (T.f_nonneg u))

end Work.ZeroFreeTables
