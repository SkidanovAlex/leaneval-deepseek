/-
# The projection of the cyclic cover commutes with reduction of paths

The cyclic cover `Γ̃` of a `ℤ`-labelled graph `Γ` (`Submission.Work.ORLocInd.Howie.CoverGraph`) has
vertex set `V × ℤ`, and `coverProjPath L p` (`Submission.Work.ORLocInd.Howie.CoverPresentation`)
projects a path of `Γ̃` starting at `p` to a path of the base graph `Γ`.

This file proves that this projection commutes with the reduction `red` of a path to its reduced
form (`Submission.Work.ORLocInd.Howie.Basic`):

**`coverProjPath_red`** : `coverProjPath L p (red P) = red (coverProjPath L p P)`.

The two ingredients are

* `coverProjPath_isReduced` (`Submission.Work.ORLocInd.Howie.coverProjPath_isReduced`): the
  projection of a reduced path is reduced;
* `coverProjPath_reducesTo` (below): the projection of a path reduces to the projection of any of
  its reducts, because a backtrack `e · e⁻¹` of the cover projects to the backtrack
  `π e · (π e)⁻¹` of the base graph (`coverProjArrow_reverse`).

The two reduced paths `coverProjPath L p (red P)` and `red (coverProjPath L p P)` are then both
reduced forms of `coverProjPath L p P`, and reduced forms are unique
(`Work.ORLocInd.Howie.red_eq_of_reducesTo_isReduced`).
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverPresentation
import Submission.Work.ORLocInd.Howie.coverProjPath_isReduced
import Submission.Work.ORLocInd.Howie.coverPath_properties

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- **A backtrack of the cover is a backtrack of the base graph.**  If `Q` is obtained from `P` by
deleting the backtrack `e · e⁻¹`, then `coverProjPath L p Q` is obtained from
`coverProjPath L p P` by deleting the backtrack `π e · (π e)⁻¹`, since the projection of the cover
is compatible with concatenation (`coverProjPath_comp`), with singleton paths
(`coverProjPath_toPath`) and with reversal (`coverProjArrow_reverse`). -/
theorem coverProjPath_deleteBacktrack (L : Labelling V) {p q : CoverVertex L}
    {P Q : Quiver.Path p q} (h : Quiver.Path.DeleteBacktrack P Q) :
    Quiver.Path.DeleteBacktrack (coverProjPath L p P) (coverProjPath L p Q) := by
  obtain ⟨x, y, p₁, e, p₂, hP, hQ⟩ :=
    Work.ORBassSerre.Path.Reduction.deleteBacktrack_cases h
  rw [hP, hQ, coverProjPath_comp, coverProjPath_comp, coverProjPath_comp,
    coverProjPath_toPath, coverProjPath_toPath, coverProjArrow_reverse, coverProjPath_comp]
  exact Quiver.Path.DeleteBacktrack.intro (coverProjPath L p p₁) (coverProjArrow e)
    (coverProjPath L x p₂)

/-- **The projection of the cyclic cover preserves reduction of paths.** -/
theorem coverProjPath_reducesTo (L : Labelling V) {p q : CoverVertex L} {P Q : Quiver.Path p q}
    (h : P.ReducesTo Q) : (coverProjPath L p P).ReducesTo (coverProjPath L p Q) := by
  induction h with
  | refl => exact Quiver.Path.ReducesTo.refl _
  | tail _ hstep ih =>
      exact Quiver.Path.ReducesTo.tail ih (coverProjPath_deleteBacktrack L hstep)

theorem coverProjPath_red {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (L : Work.ORLocInd.Howie.Labelling V) (p : Work.ORLocInd.Howie.CoverVertex L)
    {q : Work.ORLocInd.Howie.CoverVertex L} (P : Quiver.Path p q) :
    Work.ORLocInd.Howie.coverProjPath L p (Work.ORLocInd.Howie.red P) =
      Work.ORLocInd.Howie.red (Work.ORLocInd.Howie.coverProjPath L p P) := by
  refine (red_eq_of_reducesTo_isReduced (coverProjPath_reducesTo L (reducesTo_red P)) ?_).symm
  exact coverProjPath_isReduced L (red P) (isReduced_red P)

end Work.ORLocInd.Howie
