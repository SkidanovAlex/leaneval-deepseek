/-
# `Submission.Work.FIArea6T.tauRemoval6` — the τ-removal of *FI* (10.4)

This is the deliverable of the lane: `Work.FIArea6T.tauRemoval6 : Work.FITop4.TauRemoval6`.

*FI* p. 985 removes the divisor condition (5.9) `τ(|z|²) ≤ τ` from the coefficient inside the
`D₀`/`T(β)` budget, at polylogarithmic quality.  In the round-6 vocabulary this is the statement
that replacing the clean coefficient `β` by its (5.9)-truncation `tauCut Pa β` changes the cut form
`Tcut (radN Pa) cut` by at most `N²(log N)^{-19·10^8}`, uniformly over all bounded cuts (in
particular over the `U`-cut of (10.15), which is the only place the composition consumes it).

The proof assembles the four nodes of the lane:

* `Work.FIArea6T.Tcut_sesq`, the sesquilinear expansion of `Tcut`;
* `Work.FIArea6T.TcutBil_le_polar` (T2), the `L²` Schur bound `θN log²(2+N)`;
* `Work.FIArea6T.cleanCoeff_sq_mass_le` (T3), the clean second moment `N log⁷(2+N)`;
* `Work.FIArea6T.cleanTau_mass_le` (T4), the Rankin mass `N(log N)^{-4·10^9}` of the complement
  (area 7's A3, `Work.FIArea7.deltaTau_mass_le`),

via the arithmetic of `Work.FIArea6T.tau_arith_log` and the assembly
`Work.FIArea6T.tauRemoval6_core`.
-/
import Mathlib
import Submission.Work.FIArea6T.Defs
import Submission.Work.FIArea6T.TauRemoval6Core
import Submission.Work.FIArea6T.TcutBil_le_polar
import Submission.Work.FIArea6T.cleanCoeff_sq_mass_le
import Submission.Work.FIArea6T.cleanTau_mass_le

set_option autoImplicit false

namespace Work.FIArea6T

noncomputable section

/-- **The τ-removal of *FI* (10.4).** -/
theorem tauRemoval6 : Work.FITop4.TauRemoval6 := by
  obtain ⟨C3, hC3, hT3⟩ := Work.FIArea6T.cleanCoeff_sq_mass_le
  obtain ⟨x0τ, hT4⟩ := Work.FIArea6T.cleanTau_mass_le
  exact Work.FIArea6T.tauRemoval6_core C3 hC3 hT3 x0τ hT4
    (fun Pa cut u v φ hcut hu hv hθ hN =>
      Work.FIArea6T.TcutBil_le_polar Pa cut u v φ hcut hu hv hθ hN)

end

end Work.FIArea6T
