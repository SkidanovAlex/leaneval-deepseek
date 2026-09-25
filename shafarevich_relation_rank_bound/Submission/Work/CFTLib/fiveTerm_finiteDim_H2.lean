import Mathlib
import Submission.Work.CFTLib.fiveTerm_setup
import Submission.Work.CFTLib.ProP.moduleFinite_groupCohomology_trivial

/-!
# Finite-dimensionality of `H²(G, 𝔽_p)` for finite `G`

`H²(G, 𝔽_p)` is the second group cohomology of the trivial `G`-module `𝔽_p`.  For `G` finite it is
the homology of the complex of inhomogeneous cochains, which in each degree is a finite
`𝔽_p`-module; hence the cocycles (a submodule) and the cohomology (a quotient) are finite
`𝔽_p`-modules as well, i.e. finite-dimensional over the field `𝔽_p`.

This is the `H²`-analogue of
`Work.CFTLib.ProP.moduleFinite_groupCohomology_trivial`, restated for `FiniteDimensional` and the
notation `Work.CFTLib.H2`.
-/

namespace Work.CFTLib

theorem fiveTerm_finiteDim_H2 {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G] :
    FiniteDimensional (ZMod p) (Work.CFTLib.H2 p G) :=
  ProP.moduleFinite_groupCohomology_trivial p 2 G

end Work.CFTLib
