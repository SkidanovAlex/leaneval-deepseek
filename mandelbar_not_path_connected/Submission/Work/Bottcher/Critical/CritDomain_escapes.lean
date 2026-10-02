import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Green.green_pos_iff
import Submission.Work.Bottcher.Green.green_nonneg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Points of the critical domain escape

`CritDomain c = {z : G_c(z) > G_c(0)}` is the largest domain on which the Böttcher
product formula has no degenerate factor.  Here we record the elementary but
load-bearing fact that its points escape: an orbit in `CritDomain c` has
`green c z > greenParam c = G_c(0) ≥ 0`, hence `green c z > 0`, and the escape
dichotomy for the Green function (`green_pos_iff`) turns positivity of `G_c` at
`z` into divergence of `‖T_c^[n] z‖`.
-/

namespace Work.Bottcher.Critical

open LeanEval.ComplexAnalysis (Tantibar)

/-- Every point of the critical domain `{G_c > G_c(0)}` has an orbit that escapes
to infinity under the tricorn map `T_c`. -/
theorem CritDomain_escapes (c z : ℂ) (hz : z ∈ Work.Bottcher.CritDomain c) :
    Filter.Tendsto (fun n : ℕ => ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖)
      Filter.atTop Filter.atTop := by
  refine (Work.Bottcher.Green.green_pos_iff c z).mp ?_
  have h1 : Work.Bottcher.greenParam c < Work.Bottcher.green c z := hz
  rw [Work.Bottcher.greenParam_def] at h1
  exact lt_of_le_of_lt (Work.Bottcher.Green.green_nonneg c 0) h1

end Work.Bottcher.Critical
