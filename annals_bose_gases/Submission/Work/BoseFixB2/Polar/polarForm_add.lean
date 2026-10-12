import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseFixB2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.Polar

/-- **Additivity of the polar form in the first slot**, from the parallelogram law alone.

For `Q : V → ℝ` satisfying the parallelogram law (and, harmlessly, `2`-homogeneity),
the polar form `B x y = (Q (x + y) - Q (x - y)) / 4` is additive in its first argument:
`B (u + v) y = B u y + B v y`.  No homogeneity is needed for this direction. -/
theorem polarForm_add {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : V → ℝ) (hpar : ∀ x y : V, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x) (u v y : V) : (Q ((u + v) + y) - Q ((u + v) - y)) / 4 = (Q (u + y) - Q (u - y)) / 4 + (Q (v + y) - Q (v - y)) / 4 := by
  -- General additivity statement (parallelogram law only).
  have key : ∀ a b c : V,
      Q (a + b + c) - Q (a + b - c) = Q (a + c) - Q (a - c) + (Q (b + c) - Q (b - c)) := by
    intro a b c
    have p1 := hpar (a + c) b
    have p2 := hpar (a - c) b
    have p3 := hpar a (b + c)
    have p4 := hpar a (b - c)
    rw [show (a + c) + b = a + b + c by abel,
        show (a + c) - b = a - b + c by abel] at p1
    rw [show (a - c) + b = a + b - c by abel,
        show (a - c) - b = a - b - c by abel] at p2
    rw [show a + (b + c) = a + b + c by abel,
        show a - (b + c) = a - b - c by abel] at p3
    rw [show a + (b - c) = a + b - c by abel,
        show a - (b - c) = a - b + c by abel] at p4
    linarith
  have h := key u v y
  linarith

end Work.BoseFixB2.Polar
