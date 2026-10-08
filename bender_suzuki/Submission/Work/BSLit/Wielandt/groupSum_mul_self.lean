import Mathlib
import Submission.Work.BSLit.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.Wielandt

open Classical

/-- In the integral group algebra `ℤ[F]`, the sum `1_H = Σ_{h ∈ H} h` of the elements of a
subgroup `H ≤ F` is (up to the scalar `|H|`) an idempotent: `1_H * 1_H = |H| · 1_H`.

Indeed `1_H * 1_H = Σ_{x,y ∈ H} (xy)`, and for each fixed `x ∈ H` the map `y ↦ xy` is a
bijection `H → H`, so every element of `H` occurs exactly `|H|` times. -/
theorem groupSum_mul_self {F : Type*} [Group F] [Fintype F] (H : Subgroup F) :
    Work.BSLit.groupSum H * Work.BSLit.groupSum H =
      (Nat.card H : MonoidAlgebra ℤ F) * Work.BSLit.groupSum H := by
  -- Expand the product into a double sum over `H × H`, using `single a r * single b s =
  -- single (a * b) (r * s)`.
  have step1 : Work.BSLit.groupSum H * Work.BSLit.groupSum H
      = ∑ x : H, ∑ y : H, MonoidAlgebra.single ((x * y : H) : F) (1 : ℤ) := by
    rw [Work.BSLit.groupSum, Finset.sum_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [MonoidAlgebra.single_mul_single]
    simp
  rw [step1]
  -- For fixed `x`, the substitution `y ↦ x * y` is a bijection of `H`.
  have step2 : ∀ x : H, (∑ y : H, MonoidAlgebra.single ((x * y : H) : F) (1 : ℤ))
      = ∑ y : H, MonoidAlgebra.single ((y : H) : F) (1 : ℤ) := by
    intro x
    exact Equiv.sum_comp (Equiv.mulLeft x) (fun y : H => MonoidAlgebra.single ((y : H) : F) 1)
  simp only [step2]
  -- The inner sum no longer depends on `x`, so it is `|H| • 1_H = |H| * 1_H`.
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Nat.card_eq_fintype_card]

end Work.BSLit.Wielandt
