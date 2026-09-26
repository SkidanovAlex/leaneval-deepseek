import Mathlib
import Submission.Work.PTCert.Interfaces

/-!
# `SignCodes` — the letter index `pairIdx`

The Letters `b1 r k`, `1 ≤ k < NB1 r`, of `Interfaces.lean` are indexed by the ordered pairs
`(i,j)`, `i ≠ j`, of distinct elements of `Fin r` through `q = (k-1)/4` and `(i,j) = pairOf r q`.
This file defines the inverse map on the level of the index `q`, `pairIdx r i j`, needed to state
the re-encoding performed by `actL` (see `Submission/Work/PTCert/pairArith.lean` for the proof
that `pairOf` and `pairIdx` are mutually inverse).
-/

set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert

/-- The letter index of the ordered pair `(i,j)`, `i ≠ j`: `pairOf r (pairIdx r i j) = (i,j)`
and `pairIdx r (pairOf r q).1 (pairOf r q).2 = q` for `q < r * (r-1)`. -/
def pairIdx (r i j : ℕ) : ℕ := i * (r - 1) + (if j < i then j else j - 1)

end Work.PTCert
