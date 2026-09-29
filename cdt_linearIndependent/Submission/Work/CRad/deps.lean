/-
Support module for the `Work.CRad` area: re-exports the CDT definitions
(`beukersD`, `beukersUR`, `beukersRho`, `logPCoeff`, ...) that the CRad
lemmas are stated about, so that delegated statements involving them can be
elaborated by importing a module under `Submission/Work`.
-/
import Submission.CDT.LogHadamard
import Submission.CDTPlan.InterfacesC
