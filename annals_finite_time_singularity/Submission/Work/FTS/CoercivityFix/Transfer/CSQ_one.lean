/-
# `Transfer/CSQ_one.lean` — Cauchy–Schwarz at level `1`

The base case of `CSQ` (`Transfer/CoreDefs.lean`): the delivered membership-based
Cauchy–Schwarz bound for `H1IP` (`Transfer/H1IP_cs_of_mem.lean`) already has the right shape —
the `Q0Sm`-smoothness hypothesis is not needed at level `1`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.CoercivityFix.Transfer.CoreDefs
import Submission.Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **Cauchy–Schwarz at level `1`** for `H1IP`, with an `α`-free constant. -/
theorem CSQ_one (α : ℝ) (hα : 0 < α) :
    ∃ CC : ℝ, 0 < CC ∧ CSQ α 1 (Work.Coercivity.H1IP α) CC := by
  exact ⟨(10 : ℝ) ^ 22, by norm_num, fun X Y _ _ hX hY => H1IP_cs_of_mem α hα X Y hX hY⟩

end Work.FTS.CoercivityFix.Transfer
