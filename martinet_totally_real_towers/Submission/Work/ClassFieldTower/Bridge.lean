import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.ProTwoWitness
import Submission.NumberField.WeakWallRoute

/-!
# `Work.ClassFieldTower.Bridge` -- from this chapter to the main agent's wall

`Submission.NumberField.UnramifiedPro2TowerWall` is the weakest arithmetic wall of the
benchmark route: some number field `F` carries an infinite Galois `K/F` all of whose
finite-dimensional Galois subextensions are unramified.  `InfiniteProTwoExtension F` (this
chapter) is exactly that statement for the *maximal* unramified pro-`2` extension, so it
implies the wall after one line of unpacking.

Hence the single remaining input of this chapter,
`Work.ClassFieldTower.ProTwoShafarevichKochInput Kc` for `Kc = ℚ(√-30030)`, already implies the
main agent's wall `Submission.NumberField.UnramifiedPro2TowerWall`, and through it
`BoundedRdTowerWall` and the benchmark statement.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **The chapter's conclusion implies the main agent's wall.** -/
theorem unramifiedPro2TowerWall_of_infiniteProTwoExtension {F : Type} [Field F] [NumberField F]
    (h : InfiniteProTwoExtension F) : Submission.NumberField.UnramifiedPro2TowerWall := by
  obtain ⟨M, hM⟩ := h
  exact ⟨F, inferInstance, inferInstance, M.K, inferInstance, inferInstance, inferInstance,
    hM, fun L _ hfd hgal => M.unramified L hfd hgal⟩

/-- **THE BRIDGE.**  The single classical Shafarevich--Koch input for the explicit imaginary
quadratic field `Kc = ℚ(√-30030)` implies `Submission.NumberField.UnramifiedPro2TowerWall`,
hence (via `boundedRdTowerWall_of_unramifiedPro2TowerWall`) `BoundedRdTowerWall`. -/
theorem unramifiedPro2TowerWall_of_shafarevichKoch_witness
    (h : ProTwoShafarevichKochInput Kc) : Submission.NumberField.UnramifiedPro2TowerWall :=
  unramifiedPro2TowerWall_of_infiniteProTwoExtension
    (infiniteProTwoExtension_witness_of_shafarevichKoch h)

/-- **THE BRIDGE, wall form.** -/
theorem boundedRdTowerWall_of_shafarevichKoch_witness
    (h : ProTwoShafarevichKochInput Kc) : Submission.NumberField.BoundedRdTowerWall :=
  Submission.NumberField.boundedRdTowerWall_of_unramifiedPro2TowerWall
    (unramifiedPro2TowerWall_of_shafarevichKoch_witness h)

end Work.ClassFieldTower
