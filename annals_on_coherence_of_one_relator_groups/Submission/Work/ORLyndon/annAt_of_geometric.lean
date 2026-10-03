import Mathlib
import Submission.Work.ORLyndon.annAtDefs
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.mul_one_sub_of_infinite_order

/-!
# A geometric (finite-geometric-sum) factor of the root Fox vector

If the `x`-component `(∂u/∂x)_x` of the root Fox vector factors as a unit times a *finite geometric
sum*

`(∂u/∂x)_x = g * (1 + h + h ^ 2 + ⋯ + h ^ (k-1))`

and the `k`-th power `h ^ k` has **infinite order**, then `annAt K (u ^ l) u {x}` holds: no
non-zero element of `K[⟨X | u ^ l⟩]` right-annihilates that component.

The argument is the telescoping identity

`(1 + h + ⋯ + h ^ (k-1)) * (1 - h) = 1 - h ^ k`

(`geom_sum_mul_neg`): multiplying `b * (∂u/∂x)_x = 0` by `1 - h` turns the geometric sum into the
non-zero-divisor `1 - h ^ k` of a group algebra element of infinite order
(`Work.ORLyndon.mul_one_sub_of_infinite_order`), so that `b * g = 0`; as `g` is a unit of `K[G]`,
`b = 0`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

/-- **The geometric factor is a non-zero-divisor.**  If `(∂u/∂x)_x = g * ∑_{i<k} h ^ i` in
`K[⟨X | u ^ l⟩]` with `orderOf (h ^ k) = 0`, then the annihilator of `(∂u/∂x)_x` is trivial. -/
theorem annAt_of_geometric {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    {u : FreeGroup α} {l : ℕ} {x : α} (k : ℕ) (g h : OneRelatorGroup (u ^ l))
    (hfac : rootVec K (u ^ l) u x =
      MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) g *
        (∑ i ∈ Finset.range k, (MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) h) ^ i))
    (hord : orderOf (h ^ k) = 0) :
    annAt K (u ^ l) u {x} := by
  intro b hb
  -- the vanishing equation at the letter `x`
  have hb' := hb x (Set.mem_singleton x)
  rw [hfac, ← mul_assoc] at hb'
  -- telescoping: the geometric sum times `1 - h` is `1 - h ^ k`
  have htel : (∑ i ∈ Finset.range k, (MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) h) ^ i) *
      (1 - MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) h)
      = 1 - MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (h ^ k) := by
    rw [geom_sum_mul_neg (MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) h) k, map_pow]
  -- multiply the vanishing equation by `1 - h`
  have h2 : (b * MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) g) *
      (1 - MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (h ^ k)) = 0 := by
    have hc :=
      congrArg (fun z => z * (1 - MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) h)) hb'
    rw [zero_mul] at hc
    rwa [mul_assoc, htel] at hc
  -- `1 - h ^ k` is a right non-zero-divisor, `h ^ k` having infinite order
  have h3 : b * MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) g = 0 :=
    mul_one_sub_of_infinite_order (K := K) hord _ h2
  -- cancel the unit `of g`
  calc b = b * (MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) g *
        MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) g⁻¹) := by
        rw [← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = (b * MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) g) *
        MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) g⁻¹ := by rw [mul_assoc]
    _ = 0 := by rw [h3, zero_mul]

end Work.ORLyndon
