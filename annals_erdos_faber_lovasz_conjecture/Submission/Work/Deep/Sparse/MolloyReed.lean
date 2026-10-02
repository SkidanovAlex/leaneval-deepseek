/-
# The Molloy--Reed input of the final assembly, discharged

`ErdosFaberLovaszConjecture.MolloyReedStatement` (`Submission/EFL/LocallySparse.lean`) is one of
the four deep inputs of `Submission.theorem_1_1`.  This module records that it follows from the
theorem proved in this chapter: `molloyReedStatement_of_sparse` (`Submission/Deep/Reed.lean`)
converts the `δ`-sparse bound `SparseGraphStatement` proved in `ncp_pt.lean`/`Final.lean` into
the form consumed by the assembly, so the constant `1/e⁶` of `MolloyReedStatement` and its
`Δ`-only bound are both weaker than the `1/100` and `Δ+1` of the chapter's theorem.
-/
import Submission.Work.Deep.Sparse.Final

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Deep.Sparse

/-- **The Molloy--Reed input of the final assembly**, proved. -/
theorem molloyReedStatement : ErdosFaberLovaszConjecture.MolloyReedStatement :=
  ErdosFaberLovaszConjecture.molloyReedStatement_of_sparse sparseGraphStatement

end Work.Deep.Sparse
