import Submission.NK.GlobalCFT.Place
import Submission.Work.Kummer.Defs
import Submission.Work.SSGRoute.LocalFieldArith.finite_units_quotient_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Imports for the arithmetic inputs of `Work.SSGRoute.ext_localUnits_finite`

A single `Submission/Work`-side module re-exporting the (outside-`Submission/Work`) files needed to
*state* the finiteness of `K_wˣ / (K_wˣ)^p` and of the `p`-torsion of `K_wˣ`, so that the two
lemmas `Work.SSGRoute.localField_units_pQuotient_finite` and
`Work.SSGRoute.localField_units_pTorsion_finite` can be stated with a `Submission/Work`-side
dependency.

Nothing is proved here.
-/
