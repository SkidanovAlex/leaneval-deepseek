import Submission.Work.Cohomology.CompatTrans.dualZ

/-!
# Alias module for `CompatTrans.dualZCompat`

`Submission/Work/Cohomology/CompatTrans/relComplexIsoDualZ.lean` imports
`Submission.Work.Cohomology.CompatTrans.dualZCompat`, but the declarations `dualZObjCompat`,
`dualZCompat`, `dualZMapCompat`, … live in the module
`Submission.Work.Cohomology.CompatTrans.dualZ` (the file `dualZ.lean`, whose declarations were
renamed `dualZ` → `dualZCompat` during the split off `localCohomology`).  This module is the
missing link: it simply re-exposes that module so that the import path resolves.

The declarations themselves are declared in exactly one module, so no duplicate-declaration hazard
is introduced.
-/
