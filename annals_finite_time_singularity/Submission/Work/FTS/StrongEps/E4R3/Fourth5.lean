import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Flow5Leaves.IP4Flow
import Submission.Work.FTS.StrongEps.E4R3.fourthChapterBF_leaf
import Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Fourth5.lean` — H4 over the flow class (`FourthChapterBF`)

curric-46 install 2026-10-12 (`cbc/fts_regularity_interface.md` §5 step 3).  The restatement of
`E4R4.fourthChapterB_leaf` (`E4R3/Fourth4.lean`, left in place, now OFF the cone) with the solution
class strengthened by `EpsFlowP` (one added hypothesis on `g`, inside `AprioriPFourthBF`).
Route: the proved barrier chain (`unifIPO_IP4_of_transfer`, `apriori_fourth_of_barrier_open`,
`Pz_Jeps_lt_ratio`, `h0_of_datum_ratio_open`) with `hderiv` from LEAF-C
`IP4_JfamP_hasDerivWithinAt_of_flow` (`E4R3/Flow5Leaves/IP4Flow.lean`, PROVED) and `hneg` from
`Apriori4Proofs/energyNegJfamP` + the **proved** N4 pairing on the honest class
`E4R3/n4Pair_classC` (the `N4C/` port of the `GalClass` rows, 2026-10-12).

**PROVED** (2026-10-12) in the sibling module `E4R3/fourthChapterBF_leaf.lean`; the declaration
below is re-pointed at it, so this file no longer carries a `sorry`. -/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R5

open Work.FTS.StrongEps

set_option autoImplicit false

/-- **H4 over `EpsFlowP`**: the level-four half above a `C₀`-threshold. -/
theorem fourthChapterBF_leaf {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ → FourthChapterBF Ce Cs C₀ ρ :=
  Work.FTS.StrongEps.E4R3.fourthChapterBF_leaf hρ

end Work.FTS.StrongEps.EpsE4Thr.E4R5
