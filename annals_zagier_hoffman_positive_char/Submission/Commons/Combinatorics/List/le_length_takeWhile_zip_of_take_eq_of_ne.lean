import Submission.Commons.Combinatorics.List.le_length_zip_takeWhile_of_take_eq

/-!
# Common-prefix length of `zip`-`takeWhile`

If two lists `a b` agree on their first `k` entries but are distinct, then the length of the
common prefix computed as the `takeWhile` of the pointwise equality predicate along `a.zip b`
is at least `k`.

This is a restatement of `Commons.Combinatorics.List.le_length_zip_takeWhile_of_take_eq`.
-/

namespace Commons.Combinatorics.List

theorem le_length_takeWhile_zip_of_take_eq_of_ne {α : Type*} [DecidableEq α] {a b : List α}
    {k : ℕ} (h : a.take k = b.take k) (hne : a ≠ b) :
    k ≤ ((a.zip b).takeWhile (fun p : α × α => p.1 = p.2)).length :=
  le_length_zip_takeWhile_of_take_eq h hne

end Commons.Combinatorics.List
