import Mathlib
import Submission.Work.CNum.Fx

/-!
# `Work.CNum.IsqrtSpec` — specification of the binary-search integer square root

`Work.CNum.isqrt n = isqAux n 70 0 (n + 1)` performs a 70-step binary search for `⌊√n⌋`, which is
enough for `n < 2 ^ 70`.  Here we prove the specification used by the CNum certificate:

`isqrt n * isqrt n ≤ n < (isqrt n + 1) * isqrt (n + 1)`.

The proof is by the usual loop invariant: throughout the search the answer is confined to the
interval `[lo, hi]` (`lo² ≤ n < hi²`) and the width bound `hi ≤ lo + 2 ^ k` is halved at every step;
after 70 steps the width bound reads `hi ≤ lo + 1`, which together with `lo² ≤ n < hi²` yields the
claim.
-/

namespace Work.CNum

/-- **Loop invariant of the binary search.**  Whenever `lo * lo ≤ n < hi * hi` and
`hi ≤ lo + 2 ^ k`, the value returned by `isqAux n k lo hi` (which therefore has to lie in
`[lo, hi]`) satisfies the square-root specification for `n`. -/
lemma isqAux_spec (n : ℕ) : ∀ k lo hi : ℕ, hi ≤ lo + 2 ^ k → lo * lo ≤ n → n < hi * hi →
    (isqAux n k lo hi) * (isqAux n k lo hi) ≤ n ∧
      n < (isqAux n k lo hi + 1) * (isqAux n k lo hi + 1) := by
  intro k
  induction k with
  | zero =>
      intro lo hi hw h1 h2
      have h0 : isqAux n 0 lo hi = lo := by rw [isqAux]
      rw [h0]
      refine ⟨h1, ?_⟩
      have : hi * hi ≤ (lo + 1) * (lo + 1) := by nlinarith
      exact lt_of_lt_of_le h2 this
  | succ k ih =>
      intro lo hi hw h1 h2
      have he : isqAux n (k + 1) lo hi =
          (if ((lo + hi) / 2) * ((lo + hi) / 2) ≤ n then isqAux n k ((lo + hi) / 2) hi
           else isqAux n k lo ((lo + hi) / 2)) := by rw [isqAux]
      rw [he]
      have hw' : hi ≤ lo + 2 ^ k * 2 := by rwa [pow_succ] at hw
      by_cases hm : ((lo + hi) / 2) * ((lo + hi) / 2) ≤ n
      · rw [if_pos hm]
        exact ih ((lo + hi) / 2) hi (by omega) hm h2
      · rw [if_neg hm]
        exact ih lo ((lo + hi) / 2) (by omega) h1 (by omega)

/-- The integer square root `isqrt n = isqAux n 70 0 (n + 1)` of `n < 2 ^ 70` satisfies
`isqrt n * isqrt n ≤ n < (isqrt n + 1) * (isqrt n + 1)`. -/
theorem IsqrtSpec (n : ℕ) (hn : n < 2 ^ 70) : isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) := by
  have h2 : n < (n + 1) * (n + 1) := by nlinarith
  have h := isqAux_spec n 70 0 (n + 1) (by simpa using Nat.succ_le_of_lt hn) (Nat.zero_le n) h2
  simpa only [isqrt] using h

end Work.CNum
