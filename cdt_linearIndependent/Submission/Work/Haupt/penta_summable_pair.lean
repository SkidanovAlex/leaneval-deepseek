import Mathlib
import Submission.Work.Haupt.pentagonal_prelim

/-!
# Summability of the paired pentagonal series

`∑_{k ≥ 0} (-1)^k (q^{P(-k)} - q^{P(k+1)})`, where `P(n) = n(3n-1)/2` is the generalized
pentagonal number, converges absolutely for `‖q‖ < 1`: both `P(-k) ≥ k` and `P(k+1) ≥ k+1`
(`Work.Haupt.le_pentagonal_neg`, `Work.Haupt.le_pentagonal_add_one`), so the `k`-th term is
dominated in norm by `‖q‖^k + ‖q‖^{k+1}`, a sum of two geometric series.
-/

namespace Work.Haupt

lemma penta_summable_pair (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun k : ℕ => (-1 : ℂ) ^ k *
      (q ^ pentagonal (-(k : ℤ)) - q ^ pentagonal ((k : ℤ) + 1))) := by
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
  have hq1 : ‖q‖ ≤ 1 := le_of_lt hq
  refine Summable.of_norm_bounded (g := fun k : ℕ => ‖q‖ ^ k + ‖q‖ ^ (k + 1)) ?_ ?_
  · have h1 : Summable (fun k : ℕ => ‖q‖ ^ (k + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0 hq)
    exact (summable_geometric_of_lt_one hq0 hq).add h1
  · intro k
    have hnorm : ‖(-1 : ℂ) ^ k‖ = 1 := by simp
    calc ‖(-1 : ℂ) ^ k * (q ^ pentagonal (-(k : ℤ)) - q ^ pentagonal ((k : ℤ) + 1))‖
        = ‖q ^ pentagonal (-(k : ℤ)) - q ^ pentagonal ((k : ℤ) + 1)‖ := by
          rw [norm_mul, hnorm, one_mul]
      _ ≤ ‖q ^ pentagonal (-(k : ℤ))‖ + ‖q ^ pentagonal ((k : ℤ) + 1)‖ := norm_sub_le _ _
      _ = ‖q‖ ^ pentagonal (-(k : ℤ)) + ‖q‖ ^ pentagonal ((k : ℤ) + 1) := by
          rw [norm_pow, norm_pow]
      _ ≤ ‖q‖ ^ k + ‖q‖ ^ (k + 1) :=
          add_le_add (pow_le_pow_of_le_one hq0 hq1 (le_pentagonal_neg k))
            (pow_le_pow_of_le_one hq0 hq1 (le_pentagonal_add_one k))

end Work.Haupt
