import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical

/-- Summing a function on `H` that picks out the single preimage of `z` under the subtype
coercion `H → G`: the sum is `φ` at that preimage when `z ∈ H`, and `0` otherwise. -/
theorem sum_ite_subtype_eq {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (φ : H → ℂ) (z : G) :
    (∑ h : H, (if (h : G) = z then φ h else 0)) =
      if hz : z ∈ H then φ ⟨z, hz⟩ else 0 := by
  by_cases hz : z ∈ H
  · rw [dite_eq_left hz]
    rw [Finset.sum_eq_single ⟨z, hz⟩
      (fun b _ hb => by rw [ite_eq_right]; intro h; exact hb (Subtype.coe_injective h))
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  · rw [dite_eq_right hz]
    refine Finset.sum_eq_zero (fun h _ => ?_)
    rw [ite_eq_right]
    intro hh
    exact hz (hh ▸ h.2)

end Work.Induction
