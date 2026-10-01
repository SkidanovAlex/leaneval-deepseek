import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.TestFn_F_antitone

namespace Work.ZeroFreeTables

/-- The arithmetic contradiction underlying the `TestFn 7.2` table computation.

If a test function has `f 0 = 56/75`, `F 0 = 8/9` and `F (-7/10) = 8/5`, then for
every `λ₁ ≤ 7/10` the inequality

`0 ≤ 2 F(-λ₁) - 4 F(0) + f(0) (2(1/6 + 10⁻⁶) + 3/100)`

fails.  Indeed `F` is antitone (`TestFn_F_antitone`), so `F(-λ₁) ≤ F(-7/10) = 8/5`,
and the right hand side is then at most

`2·(8/5) - 4·(8/9) + (56/75)·(2(1/6 + 10⁻⁶) + 3/100) = -0.084265… < 0`. -/
theorem tf72_arith_false {T : TestFn} {lam₁ : ℝ}
    (hf0 : T.f 0 = 56/75) (hF0 : T.F 0 = 8/9) (hF7 : T.F (-(7/10)) = 8/5)
    (hlam₁ : lam₁ ≤ 7/10)
    (hineq : 0 ≤ 2 * T.F (-lam₁) - 4 * T.F 0
      + T.f 0 * (2 * (1/6 + 1/1000000) + 3 * (1/100))) : False := by
  have hanti := TestFn_F_antitone T
  have hle : T.F (-lam₁) ≤ 8/5 := by
    have h := hanti (show (-(7/10) : ℝ) ≤ -lam₁ by linarith)
    rwa [hF7] at h
  have hneg : 2 * T.F (-lam₁) - 4 * T.F 0
      + T.f 0 * (2 * (1/6 + 1/1000000) + 3 * (1/100)) < 0 := by
    rw [hF0, hf0]
    linarith
  linarith

end Work.ZeroFreeTables
