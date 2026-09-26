import Mathlib
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.Work.Drive.fiveCollinearBadSet
import Submission.Work.Drive.noFiveCollinear_bad_interior_empty
import Submission.Work.Drive.genericNoInflNoFiveDense_of_bad5

/-!
# The density of generic, non-inflected, five-collinear-free approximants

Combines the two *proved* halves of the `NoFiveCollinear` clause of the generic reduction:

* `Work.Drive.noFiveCollinear_bad_interior_empty` — the bad set `Work.Drive.bad5 r ρ k` (coefficients
  in the ball `Kv ρ` for which the perturbed curve has five collinear points at parameters that are
  pairwise `1/(k+1)`-separated) has empty interior (the rank `6 > 5` dimension count of
  `rank_fivePsi_slice`), and
* `Work.Drive.genericNoInflNoFiveDense_of_bad5` — the Baire assembly turning that empty-interior
  statement into the density statement.

The two halves are definitionally matched (`bad5` is the set named by the hypothesis `h5`), so the
instantiation is `fun r hr ρ hρ hS k => noFiveCollinear_bad_interior_empty hr hρ hS k`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- **The density of generic non-inflected five-collinear-free approximants.** -/
theorem genericNoInflNoFiveDense_proved : GenericNoInflNoFiveDense :=
  genericNoInflNoFiveDense_of_bad5
    (fun r hr r₀ hr₀ hS k => noFiveCollinear_bad_interior_empty hr hr₀ hS k)

end

end Work.Drive
