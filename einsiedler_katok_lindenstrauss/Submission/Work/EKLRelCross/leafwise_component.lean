import Mathlib
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.leafwise_exists
import Submission.Work.EKLRelCross.leafwise_crossSection
import Submission.Work.EKLRelCross.leafwise_luzin
import Submission.Work.EKLRelCross.leafwise_unique
import Submission.Work.EKLRelCross.leafwise_propor
import Submission.Work.EKLRelCross.leafwise_acovariant
import Submission.Work.EKLRelCross.leafwise_entropy_cs
import Submission.Work.EKLRelCross.leafwise_ergodic
import Submission.Work.EKLRelCross.leafwise_invariant

/-!
# `Work.EKLRelCross.leafwise_component` — C5: existence of leafwise measures (Pisa §5–6)

Component C5 of the frozen EKL contract is

`Work.EKLContract.P_Leafwise`,
and the planned deliverable (ROUTE_LEAD, table row C5) is `Work.EKLContract.P_X3 → P_Leafwise`.

This file is the assembly.  The pieces it needs are stated in this namespace:

* `locallyFree_of`         — local freeness of every subgroup action, from `P_X3`;
* `ae_free_orbit`          — (U2) a.e. free `U`-orbits, from Poincaré recurrence + local
                             freeness (Pisa 7.12);
* `leafwise_exists`        — existence of a leafwise system for `(μ,U,t0)` (Pisa Thm 6.3);
* `leafwise_unique`        — (U1);
* `leafwise_crossSection`  — (U3);
* `leafwise_invariant`     — (U4);
* `leafwise_propor`        — (U5) = EKL (8);
* `leafwise_luzin`         — (U6);
* `leafwise_acovariant`    — (U7) = EKL (4)/Pisa 7.16;
* `leafwise_ergodic`       — (U8);
* `leafwise_entropy_cs`    — (U9) = EKL (9).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract
open Work.EKLContract.Lemmas

/-- **C5 (frozen)** — the assembly of `P_Leafwise` from the pieces above. -/
theorem leafwise_component : Work.EKLContract.P_X3 → Work.EKLContract.P_Leafwise := by
  intro h2 μ hμ U hU t0 ht0 hcontr
  refine ⟨leafwise_exists h2 μ U hU t0 ht0 hcontr, ?_⟩
  intro ν X' hL
  exact ⟨leafwise_unique h2 μ U hU t0 ht0 hcontr ν X' hL,
         ae_free_orbit h2 μ U hU t0 ht0 hcontr,
         leafwise_crossSection h2 μ U hU t0 ht0 hcontr ν X' hL,
         leafwise_invariant h2 μ U hU t0 ht0 hcontr ν X' hL,
         leafwise_propor h2 μ U hU t0 ht0 hcontr ν X' hL,
         leafwise_luzin h2 μ U hU t0 ht0 hcontr ν X' hL,
         leafwise_acovariant h2 μ U hU t0 ht0 hcontr ν X' hL,
         leafwise_ergodic h2 μ U hU t0 ht0 hcontr ν X' hL,
         leafwise_entropy_cs h2 μ U hU t0 ht0 hcontr ν X' hL⟩

end Work.EKLRelCross
