/-
# `Pvec` — the twenty summands of `N` as a single `Fin 20`-vector

`Work.FTS.Nonlinear.Pieces.rl1Tools.Nsplit` splits the nonlinearity
`N α (Ftot α g) (Φs + Φg)` into the twenty summands `N_i^{gg}, N_i^{gs}, N_i^{sg}, N_i^{ss}`
(`i = 1..5`) of `Work.FTS.Nonlin.Defs`.  The `L¹(r⁻¹dr)`-triangle inequality
(`rl1Tools.FaSum`) and the finite-sum manipulations of the assembly are most conveniently
phrased for a *vector* `p : Fin 20 → Fn` rather than for the twenty named pieces, so this file
fixes the enumeration once and for all.

The order is grouped by the index `i` of `N_i`:

`0 = N₁^{gg}, 1 = N₁^{gs}, 2 = N₁^{sg}, 3 = N₁^{ss}, 4 = N₂^{gg}, …, 19 = N₅^{ss}`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Submission.Work.FTS.Nonlinear.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

open Work.FTS.Galerkin (Fn)

/-- The twenty summands of `N`, enumerated in the order
`N₁^{gg}, N₁^{gs}, N₁^{sg}, N₁^{ss}, N₂^{gg}, …, N₅^{ss}`. -/
def pv (α : ℝ) (g Φs Φg : Fn) : Fin 20 → Fn :=
  ![Work.FTS.Nonlin.N1gg α g Φg, Work.FTS.Nonlin.N1gs α g Φg,
    Work.FTS.Nonlin.N1sg α Φs g, Work.FTS.Nonlin.N1ss α Φs,
    Work.FTS.Nonlin.N2gg α g Φg, Work.FTS.Nonlin.N2gs α g Φg,
    Work.FTS.Nonlin.N2sg α Φs g, Work.FTS.Nonlin.N2ss α Φs,
    Work.FTS.Nonlin.N3gg α g Φg, Work.FTS.Nonlin.N3gs α g Φg,
    Work.FTS.Nonlin.N3sg α Φs g, Work.FTS.Nonlin.N3ss α Φs,
    Work.FTS.Nonlin.N4gg α g, Work.FTS.Nonlin.N4gs α g,
    Work.FTS.Nonlin.N4sg α g, Work.FTS.Nonlin.N4ss α,
    Work.FTS.Nonlin.N5gg g, Work.FTS.Nonlin.N5gs α g,
    Work.FTS.Nonlin.N5sg α g, Work.FTS.Nonlin.N5ss α]

end Work.FTS.Nonlinear.Pieces.rl1Tools
