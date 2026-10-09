import Mathlib
import Submission.Work.ProP.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

/-- Monotonicity of the generating set of `H^p`: the `p`-th powers of a smaller subgroup
generate a subgroup of the `p`-th powers of a larger one. -/
theorem powSubgroup_mono (p : ℕ) {P : Type*} [Group P] {H K : Subgroup P} (h : H ≤ K) :
    Work.Shrinking.powSubgroup p H ≤ Work.Shrinking.powSubgroup p K := by
  unfold Work.Shrinking.powSubgroup
  exact Subgroup.closure_mono (Set.image_mono h)

theorem pCentralStep_mono (p : ℕ) {P : Type*} [Group P] {H K : Subgroup P} (h : H ≤ K) :
    Work.Shrinking.pCentralStep p H ≤ Work.Shrinking.pCentralStep p K := by
  unfold Work.Shrinking.pCentralStep
  exact sup_le_sup (powSubgroup_mono p h) (Subgroup.commutator_mono h le_rfl)

end Work.ProP
