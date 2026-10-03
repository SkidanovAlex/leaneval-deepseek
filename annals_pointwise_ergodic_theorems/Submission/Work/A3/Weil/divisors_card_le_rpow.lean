import Mathlib
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

/-!
# The divisor bound `d(n) ≪ n ^ δ`

For every real `δ > 0` there is a constant `C > 0` with

  `(n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ`   for all `n ≥ 1`.

This is the standard divisor bound: the number of divisors of `n` grows more slowly than any
positive power of `n`.  It is used throughout Area A3 — in the `k`-fold divisor bound
`Work.A3.Weil.card_factorTuples_le`, in Weyl's inequality
(`Submission.Commons.Analysis.ExponentialSums.weyl_inequality`) and in Hua's inequality
(`Submission.Commons.Analysis.ExponentialSums.hua_bound`).

The statement below is a restatement, with the harmless hypothesis `1 ≤ n` made explicit, of the
general theorem `Commons.NumberTheory.DivisorBound.card_divisors_le_rpow`, which holds for *all*
`n : ℕ`, including `n = 0` (where both sides vanish).  That theorem is proved from `Mathlib`
alone; we cite it.
-/

set_option autoImplicit false

namespace Work.A3.Weil

/-- **The divisor bound.**  For every `δ > 0` there is `C > 0` such that the number of divisors of
`n` is at most `C * n ^ δ`, uniformly in `n ≥ 1`. -/
theorem divisors_card_le_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow δ hδ
  exact ⟨C, hCpos, fun n _ => hC n⟩

end Work.A3.Weil
