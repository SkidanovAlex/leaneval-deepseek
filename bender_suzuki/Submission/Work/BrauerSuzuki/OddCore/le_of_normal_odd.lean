import Mathlib
import Submission.Work.BrauerSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.OddCore

/-- Every normal odd-order subgroup is contained in `O(G)`: `O(G)` is by definition the
supremum of the normal subgroups of odd order, and `N` is one of them. -/
theorem le_of_normal_odd {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (h : Odd (Nat.card N)) : N ≤ Submission.Blueprint.oddCore G := by
  rw [Submission.Blueprint.oddCore]
  exact le_sSup ⟨hN, h⟩

end Work.BrauerSuzuki.OddCore
