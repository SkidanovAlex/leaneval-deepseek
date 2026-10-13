/-
# `H6Row6/Pieces` — the twenty pieces of the level-six `N`-row, as an indexed family

`Npair6SupAux/NDefs.lean` names the twenty pieces `nsP0 … nsP19` of the splitting
`N α (F_*+f) (Φs+Ef) = nsum α f Ef Φs` (`Npair6SupAux/NSplit6.lean`).  For the assembly of the
row it is convenient to have them as a `ℕ`-indexed family `pcs α f Ef Φs : ℕ → Fn`, so that
the `IP6`-additivity can be iterated over `Finset.range 20` and the per-piece estimates can be
stated uniformly.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongPersist.H6Row6.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NSplit6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Row6

open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongPersist.H6Rows.Npair6SupAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The twenty pieces of the `N`-row, as a `ℕ`-indexed family (zero off `{0,…,19}`). -/
def pcs (α : ℝ) (f Ef Φs : Fn) : ℕ → Fn
  | 0 => nsP0 α Φs
  | 1 => nsP1 α Φs f
  | 2 => nsP2 α f Ef
  | 3 => nsP3 α f Ef
  | 4 => nsP4 α Φs
  | 5 => nsP5 α Φs f
  | 6 => nsP6 α f Ef
  | 7 => nsP7 α f Ef
  | 8 => nsP8 α Φs
  | 9 => nsP9 α Φs f
  | 10 => nsP10 α f Ef
  | 11 => nsP11 α f Ef
  | 12 => nsP12 α
  | 13 => nsP13 α f
  | 14 => nsP14 α f
  | 15 => nsP15 α f
  | 16 => nsP16 α
  | 17 => nsP17 α f
  | 18 => nsP18 α f
  | 19 => nsP19 α f
  | _ => 0

/-- The twenty pieces sum to `nsum`. -/
theorem pcs_sum (α : ℝ) (f Ef Φs : Fn) :
    nsum α f Ef Φs
      = ∑ k ∈ Finset.range 20, pcs α f Ef Φs k := by
  have h : (∑ k ∈ Finset.range 20, pcs α f Ef Φs k)
      = pcs α f Ef Φs 0 + pcs α f Ef Φs 1 + pcs α f Ef Φs 2 + pcs α f Ef Φs 3
        + pcs α f Ef Φs 4 + pcs α f Ef Φs 5 + pcs α f Ef Φs 6 + pcs α f Ef Φs 7
        + pcs α f Ef Φs 8 + pcs α f Ef Φs 9 + pcs α f Ef Φs 10 + pcs α f Ef Φs 11
        + pcs α f Ef Φs 12 + pcs α f Ef Φs 13 + pcs α f Ef Φs 14 + pcs α f Ef Φs 15
        + pcs α f Ef Φs 16 + pcs α f Ef Φs 17 + pcs α f Ef Φs 18 + pcs α f Ef Φs 19 := by
    simp [Finset.sum_range_succ]
  rw [h]
  funext z θ
  simp only [pcs, nsum, nsP0, nsP1, nsP2, nsP3, nsP4, nsP5, nsP6, nsP7, nsP8, nsP9, nsP10,
    nsP11, nsP12, nsP13, nsP14, nsP15, nsP16, nsP17, nsP18, nsP19, Pi.add_apply]

end Work.FTS.StrongPersist.H6Row6
