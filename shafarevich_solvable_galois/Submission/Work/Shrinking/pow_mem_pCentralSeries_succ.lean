import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Submission.Work.Shrinking.PCentral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

/-- If `x` lies in the `n`-th term of the descending `p`-central series then its `p`-th power
lies in the next term: `P_n^p ≤ P_{n+1}`.

Immediate from `Subgroup.subset_closure` and `le_sup_left`, since
`pCentralSeries p P (n+1) = pCentralStep p H = powSubgroup p H ⊔ ⁅H, ⊤⁆` and `powSubgroup p H`
is the closure of the set of `p`-th powers of elements of `H`. -/
theorem pow_mem_pCentralSeries_succ (p : ℕ) (P : Type*) [Group P] {n : ℕ} {x : P}
    (hx : x ∈ pCentralSeries p P n) : x ^ p ∈ pCentralSeries p P (n + 1) := by
  rw [pCentralSeries_succ, pCentralStep]
  exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨x, hx, rfl⟩)

end Work.Shrinking
