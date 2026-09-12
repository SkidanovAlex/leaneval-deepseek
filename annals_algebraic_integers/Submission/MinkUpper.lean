import Submission.MinkBox
import Submission.MinkGlue

noncomputable section

open Polynomial
open scoped Real BigOperators

namespace Submission.MinkUpper

open Submission.MinkBox

/-- **Upper bound** (existence; Smith prop:Mink upper half, slack allowed): there are `d`
ℚ-linearly-independent integer polynomials `Q i` of degree `≤ d−1` and bounds `mu i` on their
weighted evaluations whose product is `≤ (d:ℝ)^(C·d) · D`.

This is proved by the successive-minima machinery split across:

* `Submission.MinkEngine.mink_engine` — the coordinate successive-minima engine
  (Minkowski's second theorem, upper bound, via folded volumes);
* `Submission.MinkVol.vol_weighted_vandermonde` — the volume of the weighted Vandermonde body;
* `Submission.MinkUpperGlue.minkUpper_proved` — the assembly (greedy flags, transport,
  polynomials, constants).
-/
theorem mink_upper : minkUpper := by
  exact Submission.MinkUpperGlue.minkUpper_proved

end Submission.MinkUpper
