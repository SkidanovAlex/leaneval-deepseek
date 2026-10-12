import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Finsupp.Single
import Submission.Work.BoseFixR.FibrePeelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

/-- Gluing a particle at the end with value `k`: if the remaining labelling `τ` realises
`α.update k (α k - 1)` and `α k ≠ 0`, then `Fin.snoc τ k` realises `α`.  This is the inverse
direction of the peeling step. -/
theorem fibCount_snoc_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (α : ι →₀ ℕ)
    (k : ι) (hk : α k ≠ 0) (τ : Fin n → ι) (hτ : ∀ i, fibCount τ i = (α.update k (α k - 1)) i)
    (i : ι) : fibCount (Fin.snoc τ k) i = α i := by
  rw [fibCount_snoc' τ k i, hτ i, fibCount_update]
  by_cases h : i = k
  · rw [if_pos h, if_pos h, h]
    omega
  · rw [if_neg h, if_neg h, Nat.add_zero]

end Work.BoseFixR
