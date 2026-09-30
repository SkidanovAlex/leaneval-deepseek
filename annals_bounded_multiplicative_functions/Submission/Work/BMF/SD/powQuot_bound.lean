import Mathlib
import Submission.Work.BMF.SD.powQuot_def

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bound for `powQuot` on short intervals

Writing `powQuot n q j = ∑_{i<j} (n+q)^i n^{j-1-i}` (see `powQuot_def`), each of the
`j` summands is at most `(n+q)^(j-1)` because `n ≤ n+q`.  Hence

`powQuot n q j ≤ j · (n+q)^(j-1)`,

and since `n+q ≤ 2L` this is at most `j · 2^(j-1) · L^(j-1) ≤ 4^j L^(j-1)`.
-/

namespace Work.BMF.SD

theorem powQuot_bound (n q j L : ℕ) (hj : 1 ≤ j) (hnq : n + q ≤ 2 * L) :
    |(Work.BMF.SD.powQuot n q j : ℝ)| ≤ (4:ℝ) ^ j * (L : ℝ) ^ (j - 1) := by
  -- Bound each summand by the largest one.
  have hle : (n : ℤ) ≤ (n : ℤ) + (q : ℤ) := by omega
  have hsum : powQuot n q j ≤ (j : ℤ) * ((n : ℤ) + (q : ℤ)) ^ (j - 1) := by
    rw [powQuot]
    calc ∑ i ∈ Finset.range j, ((n : ℤ) + (q : ℤ)) ^ i * (n : ℤ) ^ (j - 1 - i)
        ≤ ∑ i ∈ Finset.range j, ((n : ℤ) + (q : ℤ)) ^ (j - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hij : i < j := Finset.mem_range.mp hi
          have h1 : (n : ℤ) ^ (j - 1 - i) ≤ ((n : ℤ) + (q : ℤ)) ^ (j - 1 - i) :=
            pow_le_pow_left₀ (by positivity) hle _
          have h2 : ((n : ℤ) + (q : ℤ)) ^ i * (n : ℤ) ^ (j - 1 - i)
              ≤ ((n : ℤ) + (q : ℤ)) ^ i * ((n : ℤ) + (q : ℤ)) ^ (j - 1 - i) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
          have hidx : i + (j - 1 - i) = j - 1 := by omega
          calc ((n : ℤ) + (q : ℤ)) ^ i * (n : ℤ) ^ (j - 1 - i)
              ≤ ((n : ℤ) + (q : ℤ)) ^ i * ((n : ℤ) + (q : ℤ)) ^ (j - 1 - i) := h2
            _ = ((n : ℤ) + (q : ℤ)) ^ (i + (j - 1 - i)) := by rw [pow_add]
            _ = ((n : ℤ) + (q : ℤ)) ^ (j - 1) := by rw [hidx]
      _ = (j : ℤ) * ((n : ℤ) + (q : ℤ)) ^ (j - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Transfer the bound to `ℝ`.
  have hsumR : (powQuot n q j : ℝ) ≤ (j : ℝ) * ((n : ℝ) + (q : ℝ)) ^ (j - 1) := by
    exact_mod_cast hsum
  have hL2 : ((n : ℝ) + (q : ℝ)) ≤ 2 * (L : ℝ) := by
    exact_mod_cast hnq
  -- `j · 2^(j-1) ≤ 4^j`.
  have hkey : (j : ℝ) * (2 : ℝ) ^ (j - 1) ≤ (4 : ℝ) ^ j := by
    have hjle : (j : ℝ) ≤ (2 : ℝ) ^ j := by
      have := Nat.lt_two_pow_self (n := j)
      exact_mod_cast (le_of_lt this)
    have h2 : (2 : ℝ) ^ (j - 1) ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc (j : ℝ) * (2 : ℝ) ^ (j - 1) ≤ (2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1) :=
          mul_le_mul_of_nonneg_right hjle (by positivity)
      _ ≤ (2 : ℝ) ^ j * (2 : ℝ) ^ j := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (4 : ℝ) ^ j := by rw [← mul_pow]; norm_num
  have hnonneg : (0 : ℝ) ≤ (powQuot n q j : ℝ) := by
    exact_mod_cast powQuot_nonneg n q j
  rw [abs_of_nonneg hnonneg]
  calc (powQuot n q j : ℝ)
      ≤ (j : ℝ) * ((n : ℝ) + (q : ℝ)) ^ (j - 1) := hsumR
    _ ≤ (j : ℝ) * (2 * (L : ℝ)) ^ (j - 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (by positivity) hL2 (j - 1)
    _ = ((j : ℝ) * (2 : ℝ) ^ (j - 1)) * (L : ℝ) ^ (j - 1) := by rw [mul_pow]; ring
    _ ≤ (4 : ℝ) ^ j * (L : ℝ) ^ (j - 1) := mul_le_mul_of_nonneg_right hkey (by positivity)

end Work.BMF.SD
