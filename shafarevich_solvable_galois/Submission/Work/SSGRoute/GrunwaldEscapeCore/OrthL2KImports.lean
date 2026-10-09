import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.InertiaCriterionImports
import Submission.Work.SSGRoute.GrunwaldEscapeCore.ProdFormulaImports
import Submission.Work.SSGRoute.ZConstruction.levelK_kummerCharHom_dictionary
import Submission.Work.SSGRoute.ZDataMup.localNormSubgroup_eq_top_of_isSplitIn
import Submission.Work.GrunwaldEscapeCore.L1Korth.idele_decomposition_tFreePart
import Submission.NK.CFTLib.HR.localNormSubgroup_ofInfinite_eq_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import hub for the `L₂ = K` orthogonality assembly

One module under `Submission/Work` collecting every vocabulary item the assembly of
`Work.SSGRoute.GrunwaldEscapeCore.orthogonality_L2K` needs: the local Kummer dictionary and its
`kummerCharHom` form, the local-norm-top criterion at split and at complex places, the idèle
decomposition of the `T'`-free part, the commutative product formula and the inertia criterion.
-/
