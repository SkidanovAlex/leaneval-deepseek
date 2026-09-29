import Mathlib
import Submission.CDTPlan.InterfacesA

/-! Bridge module for the Z3 (`phiA_inner_unique`) subtree: re-exports the Theorem-A contract
module `Submission.CDTPlan.InterfacesA` (definitions `psiA`, `phiA`, `hauptH`, ...) so that
delegated lemmas living under `Submission/Work/` can import it as a `Work`-relative dependency. -/
