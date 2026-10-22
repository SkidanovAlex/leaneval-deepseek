/-
Re-export of the blueprint interfaces for the `CWTOP` area. Delegated lemmas in this area
depend on this module (rather than on `Submission.Blueprint.Interfaces` directly), so that a
single module inside `Submission/Work/` provides both the closure class `CWClosed` and the
basic cell calculus of `Submission.Work.CWTOP.Basic`.
-/
import Submission.Blueprint.Interfaces
import Submission.Work.CWTOP.Basic
