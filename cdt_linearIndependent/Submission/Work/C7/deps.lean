import Mathlib
import Submission.CDT.Residue

/-!
# `Work.C7.deps` — shared vocabulary for the C7 (Lemma `seven`) rational-ODE work

A re-export module: `Submission.CDT.Residue` supplies the derivation `Submission.CDT.dRat` of
`K(X)`, the valuation `Submission.CDT.ordAt` at a finite point, and the residue calculus
(`Submission.CDT.ResidueAt`).  `Work/C7/rat_ode.lean` and its delegated lemmas import this module
so that their statements can be written in that vocabulary.
-/
