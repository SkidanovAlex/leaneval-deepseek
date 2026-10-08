import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic

namespace Work.CORE3

open Work.GW2

/-- Bender 1981 §2 (p. 219): `t ∈ S₀` is the central involution of the Sylow 2-subgroup `S`,
i.e. `S ≤ C_G(t) = B.H`.  (Already available as `Work.CORE2A.bSetup_S_le_H`; import
`Submission.Work.CORE2A.Basic` and cite it, or reproduce the short proof.) -/
theorem SylowLeCentralizer (G : Type) [Group G] [Finite G] (h : BenderCtx G)
    (B : BenderSetup G) : (B.S : Subgroup G) ≤ B.H := by
  exact Work.CORE2A.bSetup_S_le_H B

end Work.CORE3
