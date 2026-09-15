import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

namespace Commons.Combinatorics.Additive.Gowers

theorem cube_one_sum {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℝ) :
    (∑ x : G, ∑ h : G, f x * f (x + h)) = (∑ x : G, f x)^2 := by
  classical
  calc
    (∑ x : G, ∑ h : G, f x * f (x + h))
        = ∑ x : G, f x * (∑ h : G, f (x + h)) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [← Finset.mul_sum]
    _ = ∑ x : G, f x * (∑ h : G, f h) := by
          apply Finset.sum_congr rfl
          intro x hx
          apply congrArg (fun t : ℝ => f x * t)
          exact Equiv.sum_comp (Equiv.addLeft x) f
    _ = (∑ x : G, f x)^2 := by
          rw [← Finset.sum_mul]
          simp [pow_two]

end Commons.Combinatorics.Additive.Gowers