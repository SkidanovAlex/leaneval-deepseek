/-
# The target: `SparseGraphStatement`

This module closes the subproject `Submission/Work/Deep/Sparse/`: it derives the probabilistic
core `NCPCore` of `Submission/Work/Deep/Sparse/Assembly.lean` from the fully proved
naive-colouring-procedure theorem `Work.Deep.Sparse.ncp_core_pt`
(`Submission/Work/Deep/Sparse/ncp_pt.lean`), and hence proves

`Work.Deep.Sparse.sparseGraphStatement : ErdosFaberLovaszConjecture.SparseGraphStatement`,

the statement requested by `Submission/Deep/Reed.lean`, by way of the interface
`ErdosFaberLovaszConjecture.NCPCoreStatement` of `Submission/Deep/NCP.lean`.

The route is the one of Molloy--Reed (Chapter 10) and Bonamy--Perrett--Postle (Section 3):

* `Work.Deep.Sparse.ncp_core_pt` — the naive colouring procedure with a uniformly random
  colouring, the uncolouring of the monochromatic edges, the expectation/concentration
  analysis of `pairTerm - tripleTerm` (`Work.Deep.Sparse.concentration_ncp`,
  `Work.Deep.Sparse.ncp_concentration`) and the Lovász Local Lemma
  (`Work.Deep.Sparse.lll_apply`);
* `Work.Deep.Sparse.ncpCoreStatement_of_ncpCore` and
  `Work.Deep.Sparse.sparseGraphStatement_of_ncpCore` (`Main.lean`) — the conversion into the
  workspace's `NCPCoreStatement` and the deterministic extension step;
* `sparseGraphStatement_of_ncpCore ncpCore_of_pt` — the final assembly.
-/
import Submission.Work.Deep.Sparse.Main
import Submission.Work.Deep.Sparse.ncp_pt
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

/-- **The target theorem.**  Every finite graph `G` with `Δ(G) ≤ Δ`,
`e(G[N(v)]) ≤ (1-δ)Δ²/2` for all `v` and `Δ ≥ Δ₀ δ` (with `Δ₀` polynomially bounded in
`1/δ`) admits a proper colouring with at most `(1 - c·δ)(Δ+1)` colours, `c = 1/100`. -/
theorem sparseGraphStatement : ErdosFaberLovaszConjecture.SparseGraphStatement :=
  sparseGraphStatement_of_ncpCore ncpCore_of_pt

end Work.Deep.Sparse
