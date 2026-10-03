import Mathlib
import Submission.Work.ORHughesFree.DivisionClosure

namespace Work.ORHughesFree.DivisionClosure

/-- The approximating chain `Q₀ ⊆ Q₁ ⊆ ⋯` of the division closure is increasing. -/
theorem monotone_divisionClosureChain {S : Type*} [Ring S] (R : Set S) :
    Monotone (divisionClosureChain R) := by
  apply monotone_nat_of_le_succ
  intro n
  show (divisionClosureChain R n : Set S) ⊆ (divisionClosureChain R (n + 1) : Set S)
  intro x hx
  exact Subring.subset_closure (Set.mem_union_left _ hx)

theorem mem_divisionClosure_iff {S : Type*} [Ring S] (R : Set S) (x : S) :
    x ∈ (divisionClosure R : Set S) ↔ ∃ n, x ∈ (divisionClosureChain R n : Set S) := by
  rw [divisionClosure]
  exact Subring.mem_iSup_of_directed (monotone_divisionClosureChain R).directed_le

end Work.ORHughesFree.DivisionClosure
