/-
Re-export module.

Delegated statements in this workspace may only import modules under
`Submission/Work/`, but the corrected Nibble margin bundle `NibbleMarginsStrong`
lives in `Submission/EFL/Nibble.lean` (the paper's own chapter directory,
outside `Work/`).  Importing this module gives a delegated statement access to

* `ErdosFaberLovaszConjecture.NibbleMarginsStrong` (and the rest of
  `Submission/EFL/Nibble.lean`), and
* `Work.Deep.Nibble.AssemblyParams` (`Submission/Work/Deep/Nibble/Defs.lean`),
  the §7 assembly's numeric parameter bundle.

Nothing is defined here; it is a pure re-export.
-/
import Submission.EFL.Nibble
import Submission.Work.Deep.Nibble.Defs
