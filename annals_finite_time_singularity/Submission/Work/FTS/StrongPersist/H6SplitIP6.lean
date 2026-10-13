/-
# `Work.FTS.StrongPersist.H6SplitIP6` — discharging the `hsplit` field of `L6Ctx`

`L6Ctx` (`Clauses.lean`) carries the field

`hsplit : H6Split IP α (slice g τ) (dynRHS α Φ g τ)`,

i.e. the additivity of the pairing across the sum `linPart α f + dynRHS` of the equation's two
sides.  This is the *satisfiable* replacement of the (false) hypothesis
`HQo α 6 (linPart α (slice g τ))`: for the concrete pairing `IP6 1 … 1` the splitting follows
from the *finite-order* additivity `IP6AddFin` (proved in `IP6AddFin.lean`), which needs only
`C⁶`-smoothness and `ℋ⁶`-membership of the three slots — no `C^∞` of `𝓛_Γ^T f`.

The lemma below is the glue: it turns the two finite-order honesty facts of `linPart α f` and
`rhs` (together with the honesty of `f` itself) into the `H6Split` clause.  In the strong route
`f` and `rhs = dynRHS α Φ g τ` are `HQo α 6` (hence `C⁶` and `ℋ⁶`), and `linPart α f` is `ℋ⁶`
(the level-six membership `H6LinMem6`) and `C⁶` on the open quadrant (a regularity hypothesis on
the solution, of finite order — *not* the false `SmoothOpen`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongPersist.IP6AddFin
import Submission.Work.FTS.StrongPersist.Clauses

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`H6Split` for the concrete pairing `IP6 1 … 1`.**  From the finite-order honesty (`C⁶` on
the open quadrant) and the `ℋ⁶`-membership of the two summands `linPart α f`, `rhs` and of `f`
itself, the pairing splits across the sum. -/
theorem H6Split_IP6 {α : ℝ} {f rhs : Fn} (hα : 0 < α)
    (hl : ContDiffOn ℝ 6 (Function.uncurry (linPart α f)) Work.FTS.EllipticEst.Q0)
    (hr : ContDiffOn ℝ 6 (Function.uncurry rhs) Work.FTS.EllipticEst.Q0)
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hml : Work.Spaces.HkMem α 6 (linPart α f))
    (hmr : Work.Spaces.HkMem α 6 rhs) (hmf : Work.Spaces.HkMem α 6 f) :
    H6Split (IP6 1 1 1 1 1 1 1 1 1 1) α f rhs :=
  IP6AddFin hα hl hr hf hml hmr hmf

/-- **`hsplit` discharged for an `H6Adm` slice.**  In the strong route the slice `f` is in
`H6Adm α` (so it is `C⁶` and `ℋ⁶`), the right-hand side `rhs = dynRHS α Φ g τ` is `HQo α 6`
(hence `C⁶` and `ℋ⁶`), and `linPart α f` is `ℋ⁶` by `H6LinMem6` and `C⁶` on the open quadrant by
the (finite-order) regularity of the solution.  Under those hypotheses the `hsplit` field of
`L6Ctx` holds for the concrete pairing — so `L6Ctx` needs no `SmoothOpen` of `𝓛_Γ^T f` (which is
false, see `NOTES_L3_lin_FALSE.md`). -/
theorem H6Split_IP6_of_adm {α : ℝ} {f rhs : Fn} (hα : 0 < α)
    (hf : H6Adm α f) (hr : Work.FTS.VocabO.HQo α 6 rhs) (hlc : ContDiffOn ℝ 6 (Function.uncurry (linPart α f))
      Work.FTS.EllipticEst.Q0)
    (hml : Work.Spaces.HkMem α 6 (linPart α f)) :
    H6Split (IP6 1 1 1 1 1 1 1 1 1 1) α f rhs :=
  H6Split_IP6 hα hlc (hr.1.forall 6) (hf.reg.1.forall 6) hml hr.2 hf.reg.2

end Work.FTS.StrongPersist
