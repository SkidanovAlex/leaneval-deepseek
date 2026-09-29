import Mathlib
import Submission.HvdH.Interfaces

/-!
# Layout area: index arithmetic for `applyAlong` (paper Lemma 2.11)

A flat `A × m × B` array is indexed lexicographically, last index fastest:
element `(a,j,b)` has flat index `(a*m + j)*B + b`.

* first sort: label each element by its *slice-major* position `(a*B+b)*m + j`, so that grouping the
  sorted array into chunks of `m` gives the `A*B` slices of length `m` in slice order `s = a*B+b`;
* second sort: label each element `(s,j)` of the output slices by its flat index `(a*n + j)*B + b`
  in the `A × n × B` output layout.

The index maps and their inverses are defined here; the facts about them are stated as lemmas
(proved by other members of the team) in `Submission/Work/Layout/`.

Names: `keyIdx1` is only used through `invIdx1` (which is provably its inverse on the range).
-/

set_option autoImplicit false

namespace Work.Layout

/-- Flat index of the element `(a,j,b)` of a flat `A × m × B` array (slice-major *labelling* key of
the element at flat index `i = (a*m+j)*B + b`). -/
def keyIdx1 (m B i : ℕ) : ℕ := (i / (m * B) * B + i % B) * m + i / B % m

/-- The flat index of the element whose slice-major label is `r` (inverse of `keyIdx1`). -/
def invIdx1 (m B r : ℕ) : ℕ := (r / m / B * m + r % m) * B + r / m % B

/-- Flat index in the `A × n × B` output layout of the element `(s,j)` of the slice-major listing. -/
def tgtIdx (n B s j : ℕ) : ℕ := (s / B * n + j) * B + s % B

/-- The pair `(s,j)` (in the slice-major listing) whose output flat index is `r` (inverse of `tgtIdx`). -/
def invIdx2 (n B r : ℕ) : ℕ × ℕ := (r / (n * B) * B + r % B, r / B % n)

end Work.Layout
