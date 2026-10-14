import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.sixthChapterBF_leaf
import Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Sixth5.lean` — H6 over the flow class (`SixthChapterBF`)

curric-46 install 2026-10-12 (`cbc/fts_regularity_interface.md` §5 step 3).  The restatement of
`E4R4.sixthChapterB_leaf` (`E4R3/Sixth4.lean`, left in place, now OFF the cone) with the solution
class strengthened by `EpsFlowP` (one added hypothesis on `g`, inside `AprioriPSixthBF`).
Route: L-A `rawE6_ineq_flow` (`E4R3/Apriori4Leaves/RawE6IneqFlow.lean`, PROVED — the `hb6` it needs
is produced from the flow's `ℋ⁶`-continuity) + the PROVED `rawE6_deriv_of_flow` (S4) + L-C
`gronwall_absorb` + `IP6_cs_coeffs`; `E₁(T)` before `ε₆(T)`; the semi-tame leaf S2
`epsWP_semitame` is produced by the `E4R3/Nblock6/` chapter (`N_b6_p0`, `N_b6_p48`, `N_b6_star`,
`N_b6_rad`, `N_b6_five`, `NBlk_hkMem6`).  Uses the kernel symmetry `hρs`.

**PROVED** (2026-10-12) in the sibling module `E4R3/sixthChapterBF_leaf.lean`; the declaration
below is re-pointed at it, so this file no longer carries a `sorry`. -/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R5

open Work.FTS.StrongEps

set_option autoImplicit false

/-- **H6 over `EpsFlowP`**: the level-six half above a `C₀`-threshold. -/
theorem sixthChapterBF_leaf {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ → SixthChapterBF Ce Cs C₀ ρ :=
  Work.FTS.StrongEps.E4R3.sixthChapterBF_leaf hρ hρs

end Work.FTS.StrongEps.EpsE4Thr.E4R5
