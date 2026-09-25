import Mathlib
import Submission.Work.ShafarevichKoch.KcKochInjection
import Submission.Work.ShafarevichKoch.KcRealization
import Submission.Work.ClassFieldTower.WallShrunk

/-!
# `Work.ShafarevichKoch.KcShrunkBridge` -- the classical input in the *caller's* own vocabulary

The chapter `Submission/Work/ClassFieldTower/` (the requester of this area) consumes its arithmetic
input in the form

```
Work.ClassFieldTower.KcShrunkInput
```

-- a *discrete group* `G` with a presentation by `α` generators and `rel` relators satisfying
`rel.card ≤ #α + 1`, minimality of `α`, residual `2`-finiteness, realization of the finite
`2`-quotients by unramified extensions of `Kc`, and `5 ≤ #α` (`WallShrunk.lean`, §3).  Its own
`kcShrunkInput_of_kcWall` derives it from `KcWall = ProTwoShafarevichKochInput Kc`.

This module records that the two spellings are connected *here*, so that a caller holding the
chapter's arithmetic input (the Shafarevich--Koch injection `KochInjection M` together with
Gaschütz's value theorem, cf. `KcKochInjection.lean`) obtains the caller's wall directly, without
having to know the vocabulary of this chapter.

## Main declarations

* `Work.ShafarevichKoch.kcShrunkInput_of_kochInjection` :
  `(∃ M, KochInjection M) → (∀ M, GaschutzCohomologicalValue (G_∅)) → RealizationClauseKc →
  KcShrunkInput`.

Note the third hypothesis: the *walls* of this chapter
(`Submission.NumberField.BoundedRdTowerWall`, `UnramifiedPro2TowerWall`,
`Work.ClassFieldTower.InfiniteProTwoExtension Kc`) follow from the arithmetic input **alone**
(`KcKochInjection.lean`); only the structural `KcShrunkInput`, which asks for a *discrete* group
whose *every* finite `2`-quotient is realized by an unramified extension of `Kc`, needs the
realization clause `RealizationClauseKc` of `KcRealization.lean` in addition (the pro-`2`
presentation of `G_∅` produced by the crux realizes its quotients only through `G_∅` itself).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Classical
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **The caller's input, from this chapter's arithmetic input.**

Koch's Shafarevich--Koch injection for `G_∅ = Gal(Kc_∅/Kc)` (Koch, *Galois theory of
`p`-extensions*, Ch. 11 Thm. 11.3) together with Gaschütz's value theorem gives the presentation
interface `KcProTwoPresentationInput` of this chapter, hence the "shrunk" input
`Work.ClassFieldTower.KcShrunkInput` consumed by the unramified-tower chapter. -/
theorem kcShrunkInput_of_kochInjection
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2, KochInjection M)
    (hreal : RealizationClauseKc) :
    Work.ClassFieldTower.KcShrunkInput :=
  Work.ClassFieldTower.kcShrunkInput_of_kcWall
    (proTwoShafarevichKochInput_Kc_of_input_and_realization
      (kcProTwoPresentationInput_of_kochInjection hdict h) hreal)

end Work.ShafarevichKoch
