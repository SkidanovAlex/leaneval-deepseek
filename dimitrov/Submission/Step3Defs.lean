import Mathlib

/-!
# Step3Defs -- Step3-free home of the shared hedgehog definitions

`Step3.dirStar` (the hedgehog `⋃_{w ∈ u} [0, L·w]`) is the only symbol of
`Submission.Step3` needed by the keystone/comparison machinery
(Step3Bridge, Step3Decomp, RegularStarValue, Step3Assembly).  Those
modules used to import `Submission/Step3.lean`, which made them
un-importable BY `Step3.lean` (import cycle) and would have blocked the
final closure of `Step3.sym_maximality` once the deep comparison
(`Step3Decomp.star_fekete_limsup_le_regular`) is proved: `Step3.lean`
must be able to import the comparison content, so that content must not
depend on `Step3.lean`.  This module breaks that dependency: `dirStar`
now lives here (still in `namespace Submission.Step3`, so all existing
qualified/unqualified references resolve unchanged), `Step3.lean`
imports `Step3Defs` and no longer defines `dirStar` itself, and the
comparison modules import `Step3Defs` instead of `Step3`.

VERIFIED: 0 sorries; axioms [propext, Classical.choice, Quot.sound]
(no sorryAx); imports Mathlib only.  The statement of
`Submission.Step3.sym_maximality` is NOT touched (still in
`Submission/Step3.lean`, unchanged).
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Submission.Step3

/-- The hedgehog with spikes of length `L` in the directions `u`. -/
def dirStar (u : Finset ℂ) (L : ℝ) : Set ℂ :=
  {X : ℂ | ∃ w ∈ u, X ∈ segment ℝ 0 ((L : ℂ) * w)}

end Submission.Step3

end
