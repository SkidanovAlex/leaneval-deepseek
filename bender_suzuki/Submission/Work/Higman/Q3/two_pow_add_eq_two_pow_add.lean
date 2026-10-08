import Mathlib
import Submission.Work.Higman.Q3.two_pow_add_eq_of_eq
import Submission.Work.Higman.Q3.abs_two_pow_sub_lt

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3

/-- **Two-power sum uniqueness.** Let `M = 2 ^ n - 1`. Every exponent is `< n`, so
`2 ^ A + 2 ^ B - 2 ^ C - 2 ^ D` is a positive-or-negative integer of absolute value at most
`2 ^ n - 2 < M`. Hence if `M` divides it, it must be `0`, i.e. `2 ^ A + 2 ^ B = 2 ^ C + 2 ^ D`;
uniqueness of the binary expansion then forces the multisets `{A, B}` and `{C, D}` to agree. -/
theorem two_pow_add_eq_two_pow_add {n A B C D : ℕ} (hn : 1 ≤ n)
    (hA : A < n) (hB : B < n) (hC : C < n) (hD : D < n)
    (h : (2 ^ n - 1 : ℤ) ∣ (2 ^ A : ℤ) + 2 ^ B - 2 ^ C - 2 ^ D) :
    (A = C ∧ B = D) ∨ (A = D ∧ B = C) := by
  -- The four-term signed sum is too small (in absolute value) to be a nonzero multiple of
  -- `2 ^ n - 1`, so it vanishes.
  have hbound := abs_two_pow_sub_lt hn hA hB hC hD
  have hzero : (2 ^ A : ℤ) + 2 ^ B - 2 ^ C - 2 ^ D = 0 :=
    Int.eq_zero_of_abs_lt_dvd h hbound
  -- Reading the vanishing identity in `ℕ` gives an equality of two-power sums.
  have heq : 2 ^ A + 2 ^ B = 2 ^ C + 2 ^ D := by
    have hz : ((2 ^ A + 2 ^ B : ℕ) : ℤ) = ((2 ^ C + 2 ^ D : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast hz
  -- Uniqueness of the binary expansion of a two-power sum.
  exact two_pow_add_eq_of_eq heq

end Work.Higman.Q3
