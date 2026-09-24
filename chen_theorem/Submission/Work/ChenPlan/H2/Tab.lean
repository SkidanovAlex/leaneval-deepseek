import Submission.ChenPlan.Interfaces

/-!
# The upper-envelope table of the linear sieve, as a rational list

`tabQ` is the table `Submission.ChenPlan.utabList` of the linear-sieve upper envelope, and
`utabQ k` is its `k`-th entry (`0` outside the range).  It is exposed here so that the purely
numerical estimates on the window sum can be delegated without depending on the (fixed)
interface file.

NOTE: the entries of `Submission.ChenPlan.utabList` are already the *values* of the envelope
(`2387/1000 = 2.387`, ...), so no further division is needed when using `utabQ`.

## The window sum

The numerical core of Chen's `h2` is the estimate

`Σ_{k} utabQ k · max 0 (log (min (7/2 - k/20) (10/3) / max 1 (7/2 - (k+1)/20))) ≤ 1.551`.

The `k`-th summand is (up to the `max 0`) `Utab(s_k) · log ((σ - s_k)/(σ - s_{k+1}))` at
`σ = 5`, `s_k = 3/2 + k/20`, with the `min`/`max` clamps coming from the ends of the window
`q ∈ [M, Y)`: the numerator `7/2 - k/20 = 5 - s_k` is replaced by `10/3` when the cell reaches
past the top of the window (`min (7/2 - k/20) (10/3)`), and the denominator
`max 1 (7/2 - (k+1)/20)` corresponds to the lower end of the window `q ≥ M`.

Only `k = 3, …, 49` have a nonzero summand; the total is `≈ 1.5491499`, so the bound `1.551`
leaves a margin of `≈ 0.0019`.

A workable route: with `u = max 1 (7/2 - (k+1)/20)` and `v = min (7/2 - k/20) (10/3)`,
one has `log (v/u) ≤ (v - u) * (1/u + 1/v) / 2` (valid for `0 < u ≤ v`; it follows from
`log x ≤ x - 1` and AM–GM, `2√(uv) ≤ u + v`), and the resulting rational sum evaluates to
`≈ 1.54937 < 1.551`.
-/

namespace Work.ChenPlan.H2

/-- The linear-sieve upper-envelope table (the `utabList` of `Submission.ChenPlan`). -/
def tabQ : List ℚ := Submission.ChenPlan.utabList

/-- The `k`-th table entry, `0` if `k` is out of range. -/
def utabQ (k : ℕ) : ℚ := tabQ.getD k 0

lemma utabQ_eq (k : ℕ) : utabQ k = Submission.ChenPlan.utabList.getD k 0 := rfl

end Work.ChenPlan.H2
