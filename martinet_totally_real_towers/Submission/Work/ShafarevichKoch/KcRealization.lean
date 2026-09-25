import Mathlib
import Submission.Work.ShafarevichKoch.Kc
import Submission.Work.ShafarevichKoch.Crux
import Submission.Work.ShafarevichKoch.proTwoShafarevichKochInput_Kc_of_presentation_and_quotients

/-!
# `Work.ShafarevichKoch.KcRealization` -- item (3) of the deliverable, conditionally

The deliverable's item (3) is the unconditional `Work.ClassFieldTower.ProTwoShafarevichKochInput Kc`,
equivalently (see `README.md` §9.6) the congruence-subgroup statement that the dense subgroup
`⟨g⟩ ≤ G_∅` produced by the presentation has *all* its finite `2`-quotients realized by unramified
extensions of `Kc`.  The chapter proves the sound interface from the presentation datum plus that
one clause (`Work.ShafarevichKoch.proTwoShafarevichKochInput_Kc_of_presentation_and_quotients`),
which is stated for a *fixed* relator family `w : Fin 6 → FreeGroup (Fin 5)`.

This module packages the clause as a predicate on `Kc` alone, so that item (3) can be stated
without mentioning the presentation:

* `Work.ShafarevichKoch.RealizationClauseKc` : for every relator family `w`, every finite
  `2`-quotient of the presented abstract group `presentedGroup 5 6 w` is `Gal(L/Kc)` for a finite
  unramified Galois `L/Kc`;
* `Work.ShafarevichKoch.proTwoShafarevichKochInput_Kc_of_input_and_realization` : the crux
  (`KcProTwoPresentationInput`, item (2)) together with that clause gives item (3).

The clause is **not** a formality (README §8.5: a dense injective finitely presented subgroup of a
pro-`2` group need not have all its finite quotients extend -- `ℤ² ↪ ℤ₂`, `(m,n) ↦ n - αm`,
`α ∈ ℤ₂ ∖ ℚ`); it is the arithmetic content that item (3) has over item (2).  The walls of
`Kc.lean` do *not* need it: `InfiniteProTwoExtension Kc` and
`Submission.NumberField.BoundedRdTowerWall` follow from the crux alone (`Kc.lean`), or from
`KcClosedRelationCount` + the group-theoretic dictionary (`wall_corollaries.lean`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **The realization clause for `Kc`, as a predicate not mentioning the presentation.**

For every relator family `w : Fin 6 → FreeGroup (Fin 5)`, every finite `2`-quotient of the abstract
group `presentedGroup 5 6 w` is the Galois group of a finite unramified Galois extension of `Kc`.
This is `Work.ClassFieldTower.RealizedByUnramifiedExtensions` applied to the presented groups. -/
def RealizationClauseKc : Prop :=
  ∀ w : Fin 6 → FreeGroup (Fin 5),
    RealizedByUnramifiedExtensions Kc (presentedGroup 5 6 w)

/-- **Item (3) of the deliverable, from the crux and the realization clause.**

`KcProTwoPresentationInput` (item (2), the Shafarevich--Koch relation bound) together with the
realization clause `RealizationClauseKc` gives the sound interface
`Work.ClassFieldTower.ProTwoShafarevichKochInput Kc`. -/
theorem proTwoShafarevichKochInput_Kc_of_input_and_realization
    (h : KcProTwoPresentationInput) (hreal : RealizationClauseKc) :
    ProTwoShafarevichKochInput Kc := by
  obtain ⟨M, g, w, hker, hdense⟩ := hasProTwoPresentation_six_of_input h
  exact proTwoShafarevichKochInput_Kc_of_presentation_and_quotients M g w hker hdense (hreal w)

end Work.ShafarevichKoch
