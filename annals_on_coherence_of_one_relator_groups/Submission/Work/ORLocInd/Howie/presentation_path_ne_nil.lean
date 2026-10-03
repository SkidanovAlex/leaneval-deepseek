/-
# The relator paths of a groupoid presentation are nonempty

A `Presentation V` (Howie 2000) is a staggered groupoid presentation without proper powers;
in particular (`Presentation.notProperPower`) no relator path is a *proper power*, i.e. a
repetition of a closed path two or more times.

The empty path `Quiver.Path.nil` **is** a proper power: it is `compPower nil 2` (indeed
`compPower nil m = nil` for every `m`).  Hence no relator of a presentation can be the empty
path, which is the statement proved here.

This is used throughout the combinatorial development, where a relator is treated as a nonempty
closed path: e.g. `coverCodeList_ne_nil_of_ne_nil` and the analysis of the maximum/minimum code of
a relator (`pathMax`, `pathMin`) both rely on the relator carrying at least one arrow.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverCode

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLocInd.Howie

/-- The empty closed path is a proper power: it is `Quiver.Path.compPower Quiver.Path.nil 2`
(and in fact `Quiver.Path.compPower Quiver.Path.nil m = Quiver.Path.nil` for every `m`). -/
theorem nil_isProperPower {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V] (v : V) :
    IsProperPower (Quiver.Path.nil : Quiver.Path v v) := by
  refine ⟨Quiver.Path.nil, 2, by norm_num, ?_⟩
  simp [Quiver.Path.compPower]

/-- A relator path of a groupoid presentation is never the empty path: the empty path is a proper
power, which `Presentation.notProperPower` forbids. -/
theorem presentation_path_ne_nil {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (i : P.ι) :
    P.path i ≠ Quiver.Path.nil := by
  intro h
  exact P.notProperPower i (h.symm ▸ nil_isProperPower (P.base i))

end Work.ORLocInd.Howie
