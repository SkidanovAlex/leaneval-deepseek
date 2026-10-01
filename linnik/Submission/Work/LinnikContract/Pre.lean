/-
# LinnikContract — Pre.lean

Single import surface for the `LinnikContract` chapter: the frozen contract (`Defs`, `Areas`,
`Tables`) together with the proved Commons material that the auxiliary lemmas of this chapter
genuinely need (the critical-strip location of the non-trivial zeros, and the non-negativity of
HB's constant `B`).  Delegated lemmas may simply `import Submission.Work.LinnikContract.Pre`.
-/
import Submission.Work.LinnikContract.Tables
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.Linnik.linnikB_nonneg
