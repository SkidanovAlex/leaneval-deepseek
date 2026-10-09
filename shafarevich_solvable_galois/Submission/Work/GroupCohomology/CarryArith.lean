/-
Copyright (c) 2025. All rights reserved.

# Carries in `ℤ/n`

Two elementary arithmetic lemmas used to build the "carry" `2`-cocycle of the cyclic group
`ℤ/n` with trivial coefficients, whose transgression hits every element of `A`:

* `carry_split`: `a / n + (a % n + c) / n = (a + c) / n` (splitting a carry into two steps);
* `sum_nsmul_eq_nsmul_sum`: pulling a natural-number coefficient out of a finite sum.
-/
import Mathlib
import Submission.Work.GroupCohomology.CyclicTriv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- The number of carries when adding `a` and `c` in base `n`: splitting `(a + c) / n` into the
carry already present in `a` and the carry added by `c`. -/
theorem carry_split (n a c : ℕ) (hn : 0 < n) : a / n + (a % n + c) / n = (a + c) / n := by
  have h : a + c = n * (a / n) + (a % n + c) := by
    have := Nat.div_add_mod a n
    omega
  rw [h, Nat.mul_add_div hn]

/-- Pulling a natural number coefficient out of a finite sum: `∑ k x • b = (∑ k x) • b`. -/
theorem sum_nsmul_eq_nsmul_sum {ι : Type*} {M : Type*} [AddCommMonoid M] (s : Finset ι)
    (k : ι → ℕ) (b : M) : (∑ x ∈ s, k x • b) = (∑ x ∈ s, k x) • b := by
  classical
  refine Finset.induction ?_ ?_ s
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, add_nsmul]

end Work.GroupCohomology
