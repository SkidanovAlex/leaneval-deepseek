import Mathlib
import Submission.SecantDisk
import Submission.OPrime

/-!
# Import wrapper: the secant-triviality vocabulary

Thin re-export module so that sibling developments under `Submission/Work/` can
name, in a `depends_on` list:

* `LeanEval.KnotTheory.Quadrisecant.TrivialSecant` / `NontrivialSecant` — the
  embedded-disc (Kuperberg) notion of a topologically trivial/non-trivial secant
  (`Submission/SecantDisk.lean`), together with `ChordTrivialByArc`,
  `ChordInteriorFree`, `TrisecantTrivial`, `QuadrisecantMiddleSecantTrivial`;
* `LeanEval.KnotTheory.Quadrisecant.OPrime`, `ClassNontrivialTrisecant`,
  `ClassNontrivialMiddleSecant` (`Submission/OPrime.lean`).

Neither module is under `Submission/Work/`, so it cannot be named in a
`depends_on` list; this file puts the vocabulary one hop closer.  It contains no
declarations of its own.
-/
