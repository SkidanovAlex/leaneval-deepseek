import Mathlib
import Submission.HvdH.Interfaces

/-! Shared context for the `ResMath` area (paper §4.1–4.3(i)).

This module only re-exports `Submission.HvdH.Interfaces` (which holds `resSmat`, `resTmat`,
`permS`, `permT`, `rowSel`, `diagD`, `Nmat`, `Emat`, `Jmat`, `resA`, `diagD'`, `resB`, `dftMat`,
`rnd`, `betaR`, `ResMath1DProp`) together with Mathlib, so that lemmas requested in this area can
refer to those definitions.  Generic helper lemmas used by several sub-proofs live here too. -/

namespace Work.ResMath

end Work.ResMath
