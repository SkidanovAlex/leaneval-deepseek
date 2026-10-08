import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hall.MinimalNormal

/-- Every nontrivial finite group has a minimal normal subgroup: among the nontrivial normal
subgroups (nonempty, since `⊤` is one) pick one of least cardinality. -/
theorem hall_exists_isMinimalNormal {G : Type*} [Group G] [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, Work.Hall.IsMinimalNormal N := by
  classical
  -- the predicate "is the order of some nontrivial normal subgroup"
  have hP : ∃ n : ℕ, ∃ H : Subgroup G, H.Normal ∧ H ≠ ⊥ ∧ Nat.card H = n :=
    ⟨Nat.card (⊤ : Subgroup G), ⊤, inferInstance, top_ne_bot, rfl⟩
  obtain ⟨H, hHn, hHne, hHcard⟩ := Nat.find_spec hP
  refine ⟨H, hHn, hHne, ?_⟩
  intro M hMn hMH hMne
  -- `M` is again a nontrivial normal subgroup, so its order is at least the minimal one
  have hle : Nat.find hP ≤ Nat.card M :=
    Nat.find_min' hP ⟨M, hMn, hMne, rfl⟩
  have hcard : Nat.card M ≤ Nat.card H := Subgroup.card_le_of_le hMH
  have hEq : Nat.card M = Nat.card H := le_antisymm hcard (by rw [hHcard]; exact hle)
  -- equal order and `M ≤ H` force `M = H`
  have hMH' : M = H := Subgroup.eq_of_le_of_card_ge hMH (le_of_eq hEq.symm)
  exact le_of_eq hMH'.symm

end Work.Hall.MinimalNormal
