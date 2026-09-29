import Mathlib
import Submission.HvdH.Interfaces

/-!
# `Work.Resample.buQWwireDefs`: the uniform size bound of the `B̃` wire

`Work.Resample.buQWwire` assembles the three stage words of the one-dimensional `B̃` resampling
(`buQWsel`, `buQWrounds`, `buQWscale`, given there as abstract hypotheses) into a single program
that reads the static table `buTabList` and produces `buPhiL`.

The assembly shuffles the table entries onto the top of the value stack with `KernelLib.pick` /
`roll` / `drop`.  Every such shuffle costs at most `K * (k + 1) * (szl (window.take (k+1)) + 1)`,
so a uniform bound `buSB p α t` on the encoding size of *every* value occurring in the windows
(both the static table entries and the work vectors) converts all of them into one constant.

`buSB p α t = 10^6 (t+1)(p+4)(√p+1)(α+1)` is chosen so that

* it dominates all the table entries and the work vectors (`Work.Resample.buQWwireTabSz`,
  `Work.Resample.buQWwireVecSz`), and
* it is itself dominated by `(t+1)(p+1)^2` up to the constant `4·10^6·5`, which is what the
  cost shape `egCostShape` can afford (see `Work.Resample.buQWwireCost`).
-/

namespace Work.Resample

open HvdH

/-- The uniform size bound for all values occurring in the windows of the `B̃` wire. -/
def buSB (p α t : ℕ) : ℕ := 1000000 * (t + 1) * (p + 4) * (Nat.sqrt p + 1) * (α + 1)

end Work.Resample
