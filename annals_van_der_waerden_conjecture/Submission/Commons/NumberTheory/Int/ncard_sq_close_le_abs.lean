import Mathlib
import Submission.Commons.NumberTheory.Int.ncard_sq_close_le

namespace Commons.NumberTheory.Int

/-- The number of integers `x` with `|x^2 - y| ≤ L` is at most `4L/√|y| + 4`, when `2L ≤ |y|`
(with `|y| = y.natAbs`). -/
theorem ncard_sq_close_le_abs (y : ℤ) (L : ℕ) (h : 2 * L ≤ y.natAbs) :
    ((({x : ℤ | |x ^ 2 - y| ≤ (L : ℤ)} : Set ℤ)).ncard : ℝ)
      ≤ 4 * (L : ℝ) / Real.sqrt (y.natAbs) + 4 := by
  by_cases hn0 : y.natAbs = 0
  · -- Trivial case `y = 0`, which forces `L = 0`.
    have hy : y = 0 := Int.natAbs_eq_zero.mp hn0
    have hL : L = 0 := by
      have hle : 2 * L ≤ 0 := by rw [← hn0]; exact h
      omega
    subst hy
    subst hL
    have hset : ({x : ℤ | |x ^ 2 - (0 : ℤ)| ≤ ((0 : ℕ) : ℤ)} : Set ℤ) = {0} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hx
        have h1 : |x ^ 2| ≤ (0 : ℤ) := by simpa using hx
        have h3 : |x ^ 2| = (0 : ℤ) := le_antisymm h1 (abs_nonneg _)
        exact sq_eq_zero_iff.mp (abs_eq_zero.mp h3)
      · intro hx
        rw [hx]
        norm_num
    rw [hset, Set.ncard_singleton]
    norm_num [Real.sqrt_zero]
  · have hpos : 0 < y.natAbs := Nat.pos_of_ne_zero hn0
    rcases lt_or_ge y 0 with hyneg | hynonneg
    · -- Case `y < 0`: the set is empty, since then `x ^ 2 - y ≥ |y| ≥ 2L > L`.
      have hempty : ({x : ℤ | |x ^ 2 - y| ≤ (L : ℤ)} : Set ℤ) = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hx
        have h1 : x ^ 2 - y ≤ (L : ℤ) := (abs_le.mp hx).2
        have hx2 : (0 : ℤ) ≤ x ^ 2 := sq_nonneg x
        have hy0 : (0 : ℤ) ≤ -y := by linarith
        have hny : (y.natAbs : ℤ) = -y := by
          rw [← Int.natAbs_neg y]
          exact Int.natAbs_of_nonneg hy0
        have hnyL : (y.natAbs : ℤ) ≤ (L : ℤ) := by
          rw [hny]; linarith
        have hnl : y.natAbs ≤ L := by exact_mod_cast hnyL
        omega
      rw [hempty, Set.ncard_empty]
      simp only [Nat.cast_zero]
      positivity
    · -- Case `0 ≤ y`, so that `y = (y.natAbs : ℤ)` and the preceding lemma applies.
      have hyeq : (y.natAbs : ℤ) = y := Int.natAbs_of_nonneg hynonneg
      rw [← hyeq]
      exact ncard_sq_close_le y.natAbs L (Nat.lt_iff_add_one_le.mp hpos) h

end Commons.NumberTheory.Int
