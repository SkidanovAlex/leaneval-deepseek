import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

namespace Commons.Combinatorics.Additive.Gowers

/-- Decoupling of a bilinear sum over a finite additive group: the inner sum
`∑ h f x * g (x + h)` equals `f x * (∑ g)` because translation `h ↦ x + h` is a
bijection, so the whole double sum factors as `(∑ f) * (∑ g)`. -/
theorem bilinear_sum_decouple {G : Type*} [AddCommGroup G] [Fintype G] (f g : G → ℝ) :
    (∑ x : G, ∑ h : G, f x * g (x + h)) = (∑ x : G, f x) * (∑ x : G, g x) := by
  classical
  calc
    (∑ x : G, ∑ h : G, f x * g (x + h))
        = ∑ x : G, f x * (∑ h : G, g (x + h)) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [← Finset.mul_sum]
    _ = ∑ x : G, f x * (∑ h : G, g h) := by
          apply Finset.sum_congr rfl
          intro x hx
          apply congrArg (fun t : ℝ => f x * t)
          exact Equiv.sum_comp (Equiv.addLeft x) g
    _ = (∑ x : G, f x) * (∑ x : G, g x) := by
          rw [← Finset.sum_mul]

end Commons.Combinatorics.Additive.Gowers