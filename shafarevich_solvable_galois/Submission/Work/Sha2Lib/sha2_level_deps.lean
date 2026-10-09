/-
Shared imports for the `Sha2Lib` cyclotomic level lemmas
(`Work.Sha2Lib.inertiaDeg_cyclotomic_level` and its helper lemmas).

This module contains no declarations of its own: it merely re-exports the on-disk arithmetic
inputs (`Commons.NumberTheory.NumberField.Completion.*` in
`exists_galois_unramified_extension_of_inertiaDeg`, and the Frobenius helpers
`orderOf_frobenius_eq_inertiaDeg`, `exists_frobenius_galRestrict`, `frobenius_eq_of_commute`)
so that helper lemmas can `import Submission.Work.Sha2Lib.sha2_level_deps` and use them.
-/
import Submission.NK.NumberTheory.NumberField.Completion.exists_galois_unramified_extension_of_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.exists_frobenius_galRestrict
import Submission.Commons.NumberTheory.NumberField.frobenius_eq_of_commute
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
