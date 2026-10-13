import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.JepsIP6Transfer
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.JepsGainQuant
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.EpsWPSemitame
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.L6CtxJfamP
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.RawE6Deriv
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.RawSliceL12Zero
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.RawE6Ineq
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.GronwallAbsorb

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Sixth4.lean` — OPEN LEAF H6, the `ℋ⁶`-half of `AprioriChapter4` (low: assembly)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 H6; REVIEW F1).
From L-A in the form `rawE6_ineq_ones3` (pairing = PROVED `H6Pair_ones3`; NOT `H6Pair6`), L-C
`gronwall_absorb`, S4 `rawE6_deriv`; `E0 ≤ CC(Kα²)²` via `IP6_cs_coeffs`; `E₁(T)` is chosen before
`ε₆(T)` so the quadratic defect is absorbed.  NOTE: S4 carries an explicit uniform-in-`τ` bound
`hbdd6` (risk R2) that `EpsRegP` does not supply; `rawE6_ineq_ones3` needs `0 < Ce`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.StrongEps

set_option autoImplicit false

/-- **OPEN LEAF (H6)** the level-six half above a `C₀`-threshold. -/
theorem sixthChapterB_leaf {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ → SixthChapterB Ce Cs C₀ ρ := by
  sorry

end Work.FTS.StrongEps.EpsE4Thr.E4R4
