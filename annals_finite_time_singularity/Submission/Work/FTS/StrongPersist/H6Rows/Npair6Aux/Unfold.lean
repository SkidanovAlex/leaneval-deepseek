/-
# `Npair6Aux/Unfold.lean` — the level-six unfolding of `IP6 1…1`

`Work.FTS.TransportS.ip4_unfold_bound` is **general in the level**: for every `n`,

`|IPn α n u v| ≤ 3^n · 10^22 · SlotSum α (n+1) u v`   (`SmoothOpen u`, `SmoothOpen v`),

where `IPn α n` is the `n`-fold iterate of the paper's recursion `HkIPStep 1 1` from `H1IP`,
and `SlotSum α N u v` is the sum of the absolute values of the elementary slot pairings
`slotPairing ρ a b u v` over the slots `a + b ≤ N` and the three leaf weights of `H1IP`
(`leafEta`, `leafOne`, and `leafGam α` at the slots with `a ≥ 1`).

Since `IP6 1 1 1 1 1 1 1 1 1 1 α = HkIPStep 1 1 (HkIPStep 1 1 IP4) = IPn α 5` (definitionally),
the target's pairing is bounded by `3^5 · 10^22 · SlotSum α 6`, i.e. by a sum of elementary
slot pairings at level six.  This is the reduction that the `N`-row (`Npair6`) uses: every
piece of `N` is bounded slot by slot.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Construction.Defs
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `IP6 1 … 1` is the five-fold iterate of the recursion `HkIPStep 1 1` from `H1IP`. -/
theorem IP6_ones_eq_IPn (α : ℝ) :
    Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α = Work.FTS.TransportS.IPn α 5 := rfl

/-- **The level-six unfolding.**  The pairing `IP6 1…1` of two functions smooth on the open
quadrant is dominated by `3^5·10^22` times the sum of the absolute values of its elementary
slot pairings at level six. -/
theorem IP6_unfold_bound (α : ℝ) (u v : Fn)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u v|
      ≤ (3 : ℝ) ^ 5 * (10 : ℝ) ^ 22 * Work.FTS.TransportS.SlotSum α 6 u v := by
  have h := Work.FTS.TransportS.ip4_unfold_bound 5 α u v hu hv
  rw [IP6_ones_eq_IPn]
  simpa using h

/-- The same, for the concrete pairing written with the abbreviation of the chapter. -/
theorem IP6_unfold_bound' (α : ℝ) (u v : Fn)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u v|
      ≤ (3 : ℝ) ^ 5 * (10 : ℝ) ^ 22 * Work.FTS.TransportS.SlotSum α 6 u v :=
  IP6_unfold_bound α u v hu hv

end Work.FTS.StrongPersist.H6Rows.Npair6Aux
