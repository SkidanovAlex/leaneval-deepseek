/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — Bender §4 (8): the trichotomy (T) is PROVED

`Work.GW2.C27.eightTrich9_of_leaves` (design pass 27, `Submission/Work/_design_gw/Core27.lean`)
derives the trichotomy `Work.GW2.C27.EightTrich9Prop I` — the exact statement of
`Submission/Work/CORE4/EightTrich9.lean` — from three leaves, all three now proved:

* `Work.CORE4.TrichCore` (`TrichCoreProp`, pure `p`-group, GAP: 336 configurations, 0 failures);
* `Work.CORE4.TrichCs` (`s ∈ N(Q)` and `C_Q(s) ≤ P`);
* `Work.CORE4.TrichCP` (`C_Q(P) ≤ A`).

That closes the mathematical content of the earlier `declare_false` verdicts on `EightTrich9`:
the missed step was `C_Q(P) ≤ N_G(P) = M`.
-/
import Mathlib
import Submission.Work.CORE4.Defs27
import Submission.Work.CORE4.TrichCore
import Submission.Work.CORE4.TrichCs
import Submission.Work.CORE4.TrichCP

namespace Work.CORE4

/-- **Bender §4 (8), the trichotomy (T)**, assembled from the three proved leaves by design 27's
`eightTrich9_of_leaves`.  This is `Work.CORE4.EightTrich9`'s statement. -/
theorem EightTrich9Holds (I : Work.GW2.C4Inputs) : Work.GW2.C27.EightTrich9Prop I :=
  Work.GW2.C27.eightTrich9_of_leaves I TrichCore (TrichCs I) (TrichCP I)

end Work.CORE4
