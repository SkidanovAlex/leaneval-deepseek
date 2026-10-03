/-
# Brodskii's theorem (Brodskii 1984; Howie 2000, Theorem 3.1)

Every torsion-free one-relator group is locally indicable.  This is the base case of the
local-indicability half of node N4, and the input which
`Submission.Work.ORLocInd.Brodskii.torsionFree_subgroup_locallyIndicable` (Howie 2000,
Corollary 3.2) extends to torsion-free *subgroups* of arbitrary one-relator groups.

The proof is Howie's: the groupoid version (`Howie/theorem31.lean`,
`Work.ORLocInd.Howie.locallyIndicable_vertexGroup_codeSeparates`) gives local indicability of every
vertex group of a `CodeSeparates` staggered presentation without proper powers;
`Howie/brodskiiTorsionFreeOneRelator_of_vertexGroup.lean` reduces an arbitrary torsion-free
one-relator group to that situation (cyclically reduced conjugate, not a proper power, rose
presentation).
-/
import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.Howie.theorem31
import Submission.Work.ORLocInd.Howie.brodskiiTorsionFreeOneRelator_of_vertexGroup

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd

/-- **Brodskii's theorem.**  Every torsion-free one-relator group is locally indicable. -/
theorem brodskiiTorsionFreeOneRelator : Work.ORLocInd.BrodskiiTorsionFreeOneRelator.{u} :=
  Work.ORLocInd.Howie.brodskiiTorsionFreeOneRelator_of_vertexGroup
    (fun {V} _ _ _ P v hsep => Work.ORLocInd.Howie.locallyIndicable_vertexGroup_codeSeparates P hsep v)

end Work.ORLocInd
