/-
# Howie's Theorem 3.1 (unconditional form)

`Work.ORLocInd.Howie.locallyIndicable_vertexGroup` proves Howie's Theorem 3.1 from the two cases of
his argument (`hcase1` = the cyclic-cover descent, `hcase2` = the non-indicable case), each stated
as an explicit hypothesis.  This file instantiates them:

* `hcase1` is `Work.ORLocInd.Howie.case1_descent` (`Howie/case1_descent.lean`), the cyclic-cover
  descent (`Work.ORLocInd.Howie.case1_descent_univ` in the same file is the same statement with the
  witness graph in the universe of the input graph, and is what `case1_descent` reduces to);
* `hcase2` is `Work.ORLocInd.Howie.spanned_case2_of_case2` applied to
  `Work.ORLocInd.Howie.case2` (`Howie/case2.lean`), which removes the finiteness hypotheses using
  the datum and rewrites `¬ P.HasIndicableLabelling` in terms of non-indicability of the vertex
  group at the base vertex.

The result is the statement that Howie's Theorem 3.1 is applied to everywhere else in the
development:

    every vertex group of a `CodeSeparates` staggered groupoid presentation without proper powers
    is locally indicable.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.locallyIndicable_vertexGroup
import Submission.Work.ORLocInd.Howie.spanned_case2_of_case2
import Submission.Work.ORLocInd.Howie.case1_descent
import Submission.Work.ORLocInd.Howie.case2

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

/-- **Howie's Theorem 3.1.**  Every vertex group of a staggered groupoid presentation in which no
relator is a proper power and whose edge code separates unoriented edges is locally indicable. -/
theorem locallyIndicable_vertexGroup_codeSeparates {V : Type u} [Quiver V]
    [Quiver.HasInvolutiveReverse V] [DecidableEq V] (P : Work.ORLocInd.Howie.Presentation V)
    (hsep : P.CodeSeparates) (v : V) :
    Work.ORLocInd.Group.LocallyIndicable (P.vertexGroup v) :=
  Work.ORLocInd.Howie.locallyIndicable_vertexGroup
    Work.ORLocInd.Howie.case1_descent
    (Work.ORLocInd.Howie.spanned_case2_of_case2 Work.ORLocInd.Howie.case2)
    P hsep v

end Work.ORLocInd.Howie
