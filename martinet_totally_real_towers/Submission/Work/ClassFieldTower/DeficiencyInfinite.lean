import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.ProTwoDefs
import Submission.Work.ClassFieldTower.infinite_of_hasMinimalPresentation
import Submission.Work.ClassFieldTower.isPGroup_two_of_residuallyFiniteTwo_of_finite
import Submission.Work.ProPDeficiency.Deficiency

/-!
# `Work.ClassFieldTower.DeficiencyInfinite` -- the arithmetic crux in pure group form

The Golod--Shafarevich criterion in the exact shape in which the arithmetic supplies its
hypotheses: a group that

* has a minimal presentation by `d` generators and `r` relators with deficiency at least `-1`
  (`r ≤ d + 1`, i.e. the Shafarevich--Koch bound `r ≤ d + d₂(O_F^×)` once `d₂(O_F^×) ≤ 1`),
* has `d ≥ 5` generators (the numerical certificate coming from `rank₂ Cl(F) ≥ 5` or from a
  genus level `G_∅ ↠ (𝔽₂)^5`), and
* is residually a finite `2`-group,

is **infinite**.  Combined with `RealizedByUnramifiedExtensions` this is the whole
Golod--Shafarevich input of the class-field-tower chapter; see
`Work.ClassFieldTower.infiniteProTwoExtension_of_kcShrunkInput`.

## Main results

* `infinite_of_deficiency_le_one` -- the pure group criterion (`r ≤ d + 1`, `5 ≤ d`);
* `infinite_of_shafarevichKochBound` -- the same with the bound `r ≤ d + d₂(O_F^×)` and
  `d₂(O_F^×) ≤ 1` (the exact arithmetic shapes);
* `not_finite_of_deficiency_le_one` -- the contrapositive for finite groups.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **The arithmetic crux in pure group form.**  A residually-`2`-finite group with a minimal
presentation by `d ≥ 5` generators and `r ≤ d + 1` relators is infinite (Golod--Shafarevich). -/
theorem infinite_of_deficiency_le_one {G : Type*} [Group G] (hres : ResiduallyFiniteTwoGroup G)
    {d r : ℕ} (hpres : HasMinimalPresentation G d r) (hrel : r ≤ d + 1) (h5 : 5 ≤ d) :
    Infinite G :=
  infinite_of_hasMinimalPresentation (p := 2)
    (fun hf => isPGroup_two_of_residuallyFiniteTwo_of_finite hres hf) (by omega) hpres
    (Work.ProPDeficiency.four_mul_le_sq_of_le_add_one hrel h5)

/-- The same criterion in the exact arithmetic shapes: `ShafarevichKochBound F d r`, i.e.
`r ≤ d + d₂(O_F^×)`, together with `d₂(O_F^×) ≤ 1` (true for `F = ℚ` and imaginary quadratic
`F`, see `Work.ClassFieldTower.unitTwoRank_le_one_iff`). -/
theorem infinite_of_shafarevichKochBound {F : Type} [Field F] [NumberField F] {G : Type*}
    [Group G] (hres : ResiduallyFiniteTwoGroup G) {d r : ℕ} (hpres : HasMinimalPresentation G d r)
    (hbound : ShafarevichKochBound F d r) (hunit : unitTwoRank F ≤ 1) (h5 : 5 ≤ d) :
    Infinite G :=
  infinite_of_deficiency_le_one hres hpres (by have := hbound; simp only [ShafarevichKochBound] at hbound ⊢; omega) h5

/-- Contrapositive form, for finite groups: a finite residually-`2`-finite group with a minimal
presentation by `d ≥ 5` generators needs at least `d + 2` relators; equivalently no such group can
satisfy the Shafarevich--Koch deficiency bound when `d ≥ 5`.  This is the finite `p`-group
Golod--Shafarevich inequality in the vocabulary of this chapter, and it is what refutes the
universally quantified form of the deficiency bound (`Work.ClassFieldTower.not_kcRelationBound`):
the *finite* model `Work.ClassFieldTower.GF` satisfies all the structural hypotheses. -/
theorem not_deficiency_le_one_of_finite {G : Type*} [Group G] (hres : ResiduallyFiniteTwoGroup G)
    (hfin : Finite G) {d r : ℕ} (hpres : HasMinimalPresentation G d r) (h5 : 5 ≤ d) :
    ¬ r ≤ d + 1 := by
  intro hrel
  exact (not_finite_iff_infinite.mpr (infinite_of_deficiency_le_one hres hpres hrel h5)) hfin

end Work.ClassFieldTower
