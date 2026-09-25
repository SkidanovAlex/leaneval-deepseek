import Submission.CFTLib.Interfaces

/-!
# Re-export of the shared CFT interfaces under a `Submission.Work.*` module name

The shared class-field-theory interfaces `CFTLib.ShafBound`, `CFTLib.MaximalClassCond`,
`CFTLib.IsUnramified`, ... live in `Submission/CFTLib/Interfaces.lean` (module
`Submission.CFTLib.Interfaces`), outside the `Submission/Work/` tree that the delegation
harness can name in `depends_on`.  This module simply re-exports them, so that a lemma whose
statement mentions the CFT hypotheses can be delegated with
`depends_on := ["Submission.Work.CFTLib.Interfaces"]`.
-/
