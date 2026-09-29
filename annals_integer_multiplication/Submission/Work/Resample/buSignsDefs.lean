import Mathlib
import Submission.Work.Resample.buKit

/-!
# Definitions for `Work.Resample.buSignsWord`

`buSignsWord` realises, from a word computing the sign of one index, a word computing the whole
list of alternating signs `buL11 p α s t` from the canonical block `buCB p α s t`.

This module only fixes the *cost* bookkeeping: the uniform constant `buSignsKc` and the
intermediate cost expression `buSignsE` that the word-level proof produces, so that the pure
arithmetic bound (`Work.Resample.buSignsCost`) can be stated in a separate file.
-/

set_option autoImplicit false

namespace Work.Resample

/-- The uniform constant of the signs word. -/
def buSignsKc (Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg : ℕ) : ℕ :=
  2 ^ (Kpick + Kpush + Kswap + Ksub + Krep + Kenum + Kml + Ks + Kneg + 40)

/-- Intermediate cost bound of the signs word:

`E₁` (pick the value `n` out of the block) `+ E₂` (push `1`) `+ E₃` (swap) `+ E₄` (subtract `1`,
giving `n-1`) `+ E₅` (push `nil`) `+ E₆` (swap) `+ E₇` (`replicate (n-1) nil`) `+ E₈` (`enumerate`)
`+ E₉` (`mapList` with the element word `signProg; neg`). -/
def buSignsE (Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg p n : ℕ) : ℕ :=
  Kpick * 6 * (6 * buSZ p + 1)
    + (Kpush * 4
    + (Kswap * (buSZ p + 4)
    + (Ksub * (buSZ p + 3)
    + (Kpush * 2
    + (Kswap * (buSZ p + 4)
    + (Krep * (2 * ((n - 1) + 1) + buSZ p + 1)
    + (Kenum * (2 * ((n - 1) + 1) + (n - 1) * ((n - 1).size + 1) + 1)
    + ((n - 1) * ((Ks + Kneg + Kml) *
        (p + 1) ^ buSignsKc Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg) + Kml))))))))

end Work.Resample
