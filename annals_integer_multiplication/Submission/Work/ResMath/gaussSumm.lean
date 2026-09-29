import Mathlib

/-!
# Summability of the Gaussian over the integer lattice

`Work.ResMath.gaussSumm`: for `a > 0` and every centre `c : ℝ`, the Gaussian
`n ↦ exp (-a * (c + n) ^ 2)` is summable on `ℤ`.

This is the summability needed to make sense of the theta/Gaussian sums
`∑' n : ℤ, exp (-a * (c + n)²)` that occur throughout §4.1 of Harvey–van der Hoeven,
*Integer multiplication in time* `O(n log n)`.

Mathlib already establishes exactly this in its Jacobi theta asymptotics:
`HurwitzKernelBounds.summable_f_int k a t` says that
`n ↦ |n + a| ^ k * exp (-π * (n + a) ^ 2 * t)` is summable on `ℤ` for `t > 0`.
Taking `k = 0` (so the power is `1`) and `t = a / π` reduces `-π * (n + c) ^ 2 * t`
to `-a * (c + n) ^ 2`, which is the summand above.
-/

namespace Work.ResMath

/-- The Gaussian `n ↦ exp (-a * (c + n) ^ 2)` on `ℤ` is summable for every `a > 0` and
every centre `c`. -/
theorem gaussSumm (a : ℝ) (ha : 0 < a) (c : ℝ) :
    Summable (fun n : ℤ => Real.exp (-a * (c + (n : ℝ)) ^ 2)) := by
  -- `HurwitzKernelBounds.summable_f_int 0 c t` is summability of
  -- `n ↦ |n + c| ^ 0 * exp (-π * (n + c) ^ 2 * t)`; with `t = a / π` this is our summand.
  have ht : 0 < a / Real.pi := div_pos ha Real.pi_pos
  have h := HurwitzKernelBounds.summable_f_int 0 c ht
  refine h.congr fun b => ?_
  simp only [HurwitzKernelBounds.f_int, pow_zero, one_mul]
  rw [add_comm (b : ℝ) c]
  congr 1
  field_simp

end Work.ResMath
