import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

/-- Given two distinct elements `A ≠ B` and two distinct elements `I ≠ J` of `Fin S`, there is a
permutation of `Fin S` carrying `A` to `I` and `B` to `J`.  (Used to relabel the two distinguished
coordinates in the "collision" count of the recursion.)

Route: use products of `Equiv.swap`: `Equiv.swap B J * Equiv.swap A I` works when `I ≠ B` (check
`σ A` and `σ B` by `Equiv.swap_apply_def`-style case analysis, using `hAB`, `hIJ` and `I ≠ B`); the
remaining cases `I = B` and `J = A` are handled by similar two-swap products
(e.g. `Equiv.swap A J * Equiv.swap B J` for `J = A`).  Careful: the "if `x = A` then `I` else if
`x = B` then `J` else if `x = I` then `A` else if `x = J` then `B` else `x`" function is *not* a
bijection in the overlap cases `I = B` or `J = A`, so use swaps. -/
theorem exists_perm_pair {S : ℕ} (A B I J : Fin S) (hAB : A ≠ B) (hIJ : I ≠ J) :
    ∃ σ : Equiv.Perm (Fin S), σ A = I ∧ σ B = J := by
  by_cases h : I = B
  · -- Case `I = B`: the two-swap product `swap B J * swap A J` works.
    rw [h] at hIJ ⊢
    refine ⟨Equiv.swap B J * Equiv.swap A J, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hAB.symm hIJ, Equiv.swap_apply_left]
  · -- Case `I ≠ B`: the two-swap product `swap B J * swap A I` works.
    refine ⟨Equiv.swap B J * Equiv.swap A I, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h hIJ]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hAB.symm (Ne.symm h),
        Equiv.swap_apply_left]

end Work.BMF.recursion
