import Mathlib

/-!
# Summability of the two-sided pentagonal series `∑_{n ∈ ℤ} (-1)^n q^{n(3n-1)/2}`

We prove that `∑_{n : ℤ} (-1)^n q ^ (pentagonal n)` converges for `‖q‖ < 1`. Since the
generalized pentagonal numbers grow at least linearly in `|n|`, the `n`-th term is dominated in
norm by `‖q‖^{|n|}`, and splitting the `ℤ`-indexed series into its nonnegative and its negative
half gives two geometric series.
-/

set_option linter.dupNamespace false

namespace Work.Haupt

/-- `n ≤ pentagonal n` for `n : ℕ`. -/
private lemma le_pentagonal_natCast (n : ℕ) : n ≤ pentagonal (n : ℤ) := by
  rw [← Nat.cast_le (α := ℤ)]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp [pentagonal_def]
  · have h2 := two_mul_natCast_pentagonal (n : ℤ)
    have hprod : (0 : ℤ) ≤ (n : ℤ) * ((n : ℤ) - 1) :=
      mul_nonneg (by omega) (by omega)
    nlinarith [h2, hprod]

/-- `n ≤ pentagonal (-(n+1))` for `n : ℕ`. -/
private lemma le_pentagonal_neg_succ (n : ℕ) : n ≤ pentagonal (-((n : ℤ) + 1)) := by
  rw [← Nat.cast_le (α := ℤ)]
  have h2 := two_mul_natCast_pentagonal_neg ((n : ℤ) + 1)
  have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  nlinarith [h2, hn, sq_nonneg (n : ℤ)]

lemma penta_summable_int (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n - 1) / 2)) := by
  set r : ℝ := ‖q‖ with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; exact hq
  -- The dominating geometric-type series `∑_ℤ r ^ pentagonal n`.
  have hsum : Summable (fun n : ℤ => r ^ pentagonal n) := by
    refine Summable.of_nat_of_neg_add_one ?_ ?_
    · refine Summable.of_nonneg_of_le (fun n => pow_nonneg hr0 _) (fun n => ?_)
        (summable_geometric_of_lt_one hr0 hr1)
      exact pow_le_pow_of_le_one hr0 hr1.le (le_pentagonal_natCast n)
    · refine Summable.of_nonneg_of_le (fun n => pow_nonneg hr0 _) (fun n => ?_)
        (summable_geometric_of_lt_one hr0 hr1)
      exact pow_le_pow_of_le_one hr0 hr1.le (le_pentagonal_neg_succ n)
  refine Summable.of_norm ?_
  refine hsum.congr (fun n => ?_)
  have h1 : ‖q ^ (n * (3 * n - 1) / 2)‖ = r ^ pentagonal n := by
    rw [norm_zpow, ← hr, ← natCast_pentagonal n]
    exact zpow_natCast r (pentagonal n)
  have h2 : ‖(-1 : ℂ) ^ n‖ = 1 := by
    rw [norm_zpow]
    simp
  rw [norm_mul, h2, h1, one_mul]

end Work.Haupt

namespace Work.Haupt
namespace Work.Haupt

/-- Identical statement to `Work.Haupt.penta_summable_int`, registered under the nested
namespace produced by the file template. -/
lemma penta_summable_int (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n - 1) / 2)) :=
  _root_.Work.Haupt.penta_summable_int q hq

end Work.Haupt
end Work.Haupt
