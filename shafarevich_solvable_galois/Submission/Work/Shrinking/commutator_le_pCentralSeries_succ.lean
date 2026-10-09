import Mathlib
import Submission.Work.Shrinking.PCentral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

/-- The second defining piece of the next term: `[P_n, P] ≤ P_{n+1}`.  Also, since
`[P_n, P_n] ≤ [P_n, P]`, the quotients `P_n/P_{n+1}` are abelian.

Both inclusions are immediate from the definition
`pCentralSeries p P (n+1) = powSubgroup p H ⊔ ⁅H, ⊤⁆` and `le_sup_right`,
respectively `Subgroup.commutator_mono` with `le_top`. -/
theorem commutator_le_pCentralSeries_succ (p : ℕ) (P : Type*) [Group P] (n : ℕ) :
    ⁅pCentralSeries p P n, ⊤⁆ ≤ pCentralSeries p P (n + 1) ∧
      ⁅pCentralSeries p P n, pCentralSeries p P n⁆ ≤ pCentralSeries p P (n + 1) := by
  have h1 : ⁅pCentralSeries p P n, ⊤⁆ ≤ pCentralSeries p P (n + 1) := by
    rw [pCentralSeries_succ, pCentralStep]
    exact le_sup_right
  exact ⟨h1, le_trans (Subgroup.commutator_mono le_rfl le_top) h1⟩

end Work.Shrinking
