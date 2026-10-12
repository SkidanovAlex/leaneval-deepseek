import ChallengeDeps
import Submission.Work.BoseFixB3.Arith.b3HAbsorbRoot_holds
import Submission.Work.BoseFixB3.CS.b3CSRoot_holds
import Submission.Work.BoseFixB3.Conv.b3ConvRoot_holds
import Submission.Work.BoseFixB3.Eps.b3EpsRoot_holds
import Submission.Work.BoseFixB3.Split.b3SplitRoot_holds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Node.lean` — node D6: FS §7 `lem:Q3-splitting1`

The headline theorem of the subproject, node D6 of `BOSE_BOXNODES_LEAD.md` §2.4:

  `nodeB3B_holds` — FS §7 `lem:Q3-splitting1` (`eq:ReduceQ3`),
  `Work.BoseBoxFix.NodeB3B v h R fc`, with the single hypothesis `n ≤ 2μℓ³` on
  the state.

**Proved, sorry-free** (`#print axioms` gives `[propext, Classical.choice, Quot.sound]`).
The proof is the five-step assembly `nodeB3B_of_steps` (`Assembly.lean`) applied to
the five step theorems, one file each under this directory:

| step | file / module | theorem |
|---|---|---|
| 1 | `BoseFixB3/Split/b3SplitRoot_holds` | `Work.BoseFixB3.B3SplitRoot v h fc` |
| 2 | `BoseFixB3/CS/b3CSRoot_holds` | `Work.BoseFixB3.B3CSRoot v h R fc` |
| 3 | `BoseFixB3/Arith/b3HAbsorbRoot_holds` | `Work.BoseFixB3.B3HAbsorbRoot v` |
| 4 | `BoseFixB3/Conv/b3ConvRoot_holds` | `Work.BoseFixB3.B3ConvRoot v h R fc` |
| 5 | `BoseFixB3/Eps/b3EpsRoot_holds` | `Work.BoseFixB3.B3EpsRoot v h fc` |

This file is **not** in the import cone of `Submission.lean`; the D6 deliverable is
the theorem itself, plus the vocabulary (`Defs.lean`) and the assembly
(`Assembly.lean`, `Steps.lean`) that the rest of the BoseBox chapter consumes.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Node D6** (FS §7 `lem:Q3-splitting1`, `eq:ReduceQ3`): the renormalised `3Q`
term, the quarter of the positive `4Q` square and the `eq:DefT` budgets dominate
the low-momentum `3Q` term `Q̃₃^{(1)}` up to the `eq:ReduceQ3` error
`C μ²aℓ³(d^{2(M−1)} + R²/ℓ²)‖Φ‖²`, for every box state with `n ≤ 2μℓ³`. -/
theorem nodeB3B_holds {v : ℝ³ → ℝ} (h : ScatSol v) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 < a v) (fc : LowCut) :
    NodeB3B v h R fc :=
  nodeB3B_of_steps hav
    (Split.b3SplitRoot_holds v h fc)
    (CS.b3CSRoot_holds v h R fc hv hv1 hvrad hR hv_supp hav)
    (Arith.b3HAbsorbRoot_holds v)
    (Conv.b3ConvRoot_holds v h R fc hv hv1 hvrad hR hv_supp hav)
    (Eps.b3EpsRoot_holds v h R fc hv hv1 hvrad hR hv_supp hav)

end Work.BoseFixB3
