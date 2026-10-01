import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.LinnikAreas.JutilaPieces.S3ModelEval

/-!
# The two regions of the two-sided `S₃` boundary sum `czModelB`

`czModelB w y N` (`BzCrossDefs.lean`) is the boundary (lower cut-off) term of the two-sided `S₃`
model: it sums, over `q ≤ ⌊N/y⌋`, `r ≤ ⌊N/(q w)⌋`, `t ≤ ⌊N/(q y)⌋`, the product
`czMM r t · s3main (r*t) (log(w/t)) (log(y/r)) B`, `B = czLo w y r t = max ⌊w/t⌋ ⌊y/r⌋`.

Writing `A_t = ⌊w/t⌋₊`, `C_r = ⌊y/r⌋₊` and `B = max A_t C_r`, the summand splits into the two
regions `C_r ≥ A_t` (where `B = C_r`) and `C_r < A_t` (where `B = A_t`).  The criterion
`C_r ≥ A_t ⟺ r ≤ czD w y t := ⌊y/A_t⌋` identifies the two ranges, and after factoring
`s3main (r*t) α β B = (π²/6)⁻¹ · (r/κ(r)) · (t/κ(t)) · B · F` (`F` the logarithmic factor)
each region becomes a separate double sum `czRI`, `czRII`:

`czModelB w y N = (π²/6)⁻¹ · (czRI w y N + czRII w y N)`  (`ModelB.lean`, proved).

The two region bounds `|czRI w y N| ≤ C·N` and `|czRII w y N| ≤ C·N` are the two independent
analytic estimates into which the target `|czModelB w y N| ≤ C·N` decomposes; they are the content
of `BzCross/RegionI.lean` and `BzCross/RegionII.lean`.
-/

namespace Work.ZeroDensity.Jutila.BzCross

open Finset

noncomputable section

/-- The `F`-factor in the region `⌊y/r⌋ ≥ ⌊w/t⌋` (there `B = ⌊y/r⌋`): with
`s3main (r*t) α β B = s3c (r*t)·B·(L₁·L₂+1)` and `α = log(w/t)`, `β = log(y/r)`, this is
`(log(B t/w) − 1)(log(B r/y) − 1) + 1` at `B = ⌊y/r⌋`. -/
def czFI (w y : ℝ) (r t : ℕ) : ℝ :=
  (Real.log ((⌊y / (r : ℝ)⌋₊ : ℝ) * (t : ℝ) / w) - 1)
    * (Real.log ((⌊y / (r : ℝ)⌋₊ : ℝ) * (r : ℝ) / y) - 1) + 1

/-- The `F`-factor in the region `⌊w/t⌋ > ⌊y/r⌋` (there `B = ⌊w/t⌋`). -/
def czFII (w y : ℝ) (r t : ℕ) : ℝ :=
  (Real.log ((⌊w / (t : ℝ)⌋₊ : ℝ) * (t : ℝ) / w) - 1)
    * (Real.log ((⌊w / (t : ℝ)⌋₊ : ℝ) * (r : ℝ) / y) - 1) + 1

/-- The right end `⌊y/⌊w/t⌋⌋` of the `r`-range of the region `⌊y/r⌋ ≥ ⌊w/t⌋`: for `1 ≤ r`,
`⌊y/r⌋₊ ≥ ⌊w/t⌋₊ ↔ r ≤ czD w y t`. -/
def czD (w y : ℝ) (t : ℕ) : ℕ := ⌊y / (⌊w / (t : ℝ)⌋₊ : ℝ)⌋₊

/-- **Region I** of the two-sided boundary sum: the part of `czModelB w y N` on which the maximum
`czLo w y r t = max ⌊w/t⌋ ⌊y/r⌋` is attained by `⌊y/r⌋` (i.e. `r ≤ czD w y t`). -/
def czRI (w y : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
    ∑ r ∈ Finset.Icc 1 (min (czR w N q) (czD w y t)),
      czMM r t * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)
        * ((⌊y / (r : ℝ)⌋₊ : ℝ) * czFI w y r t)

/-- **Region II** of the two-sided boundary sum: the part of `czModelB w y N` on which
`czLo w y r t = ⌊w/t⌋` (i.e. `r > czD w y t`). -/
def czRII (w y : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
    ∑ r ∈ Finset.Icc (czD w y t + 1) (czR w N q),
      czMM r t * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)
        * ((⌊w / (t : ℝ)⌋₊ : ℝ) * czFII w y r t)

end

end Work.ZeroDensity.Jutila.BzCross
