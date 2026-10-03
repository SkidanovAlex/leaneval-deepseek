import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.F0Facts.Basic
import Submission.Work.F0Facts.Petal
import Submission.Work.F0Facts.RealOrbit
import Submission.Work.F0Facts.Connectivity
import Submission.Work.F0Facts.Orbit
import Submission.Work.F0Facts.ImmediateBasin

/-! Guidance from the project lead (the requester):

AREA F0FACTS: prove F0FactsStatement (x + x^2 is in F0 on univ; explicit Step 0 inverse orbit
avoiding -1/2).  Normal families: Submission.Work.Normal (montel_two_omitted on the slit plane).
Contracts: Submission/Work/Interfaces/Parabolic.lean (namespace MandelDim).
Blueprint: NOTES_LEAD_parabolic.md and NOTES_LEAD_fatou.md at the workspace root.
-/

namespace Work.F0Facts

open MandelDim

theorem f0facts : F0FactsStatement := by
  refine ⟨inF0_f0, orbitZ, orbitZ_zero, f0_orbitZ_succ, orbitZ_ne_zero, orbitZ_tendsto,
    orbitZ_ne_neg_half⟩

end Work.F0Facts
