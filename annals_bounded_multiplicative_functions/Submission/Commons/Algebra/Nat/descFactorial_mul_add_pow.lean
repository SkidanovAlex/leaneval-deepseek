import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Choose.Sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Algebra.Nat

/-- Taylor expansion of a power times a falling factorial: for `a, r : ℕ` and `x h : ℝ`,
`(r)↓a * (x+h)^(r-a) = ∑_{e=0}^{r-a} (r)↓(a+e) x^(r-a-e) h^e / e!`. -/
theorem descFactorial_mul_add_pow (r a : ℕ) (x h : ℝ) :
    (r.descFactorial a : ℝ) * (x + h) ^ (r - a)
      = ∑ e ∈ Finset.range (r - a + 1),
          (r.descFactorial (a + e) : ℝ) * x ^ (r - a - e) * h ^ e / (e.factorial : ℝ) := by
  rw [add_comm x h, add_pow h x (r - a), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have key : (r.descFactorial (a + e) : ℝ)
      = (r.descFactorial a : ℝ) * ((r - a).descFactorial e : ℝ) := by
    have h := Nat.descFactorial_mul_descFactorial (k := a) (m := a + e) (n := r)
      (Nat.le_add_right a e)
    rw [Nat.add_sub_cancel_left] at h
    have hh : ((r - a).descFactorial e * r.descFactorial a : ℝ)
        = (r.descFactorial (a + e) : ℝ) := by exact_mod_cast h
    rw [← hh]
    ring
  have key2 : ((r - a).descFactorial e : ℝ)
      = (e.factorial : ℝ) * ((r - a).choose e : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
  rw [key, key2]
  have hfac : (e.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero e
  field_simp

end Commons.Algebra.Nat