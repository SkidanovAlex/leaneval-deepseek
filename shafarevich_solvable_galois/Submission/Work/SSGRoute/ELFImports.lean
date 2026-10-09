import Submission.NK.GlobalCFT.Place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Imports for the arithmetic inputs of `Work.SSGRoute.ext_localUnits_finite`

A single `Submission/Work`-side module re-exporting the (outside-`Submission/Work`) file needed to
*state* the finiteness of the `p`-torsion of `K_wˣ`, so that
`Work.SSGRoute.localField_units_pTorsion_finite` can be requested with a `Submission/Work`-side
dependency.

Nothing is proved here.
-/
