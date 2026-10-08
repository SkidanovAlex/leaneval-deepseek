import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hall.SchurZassenhaus

/-- Every nontrivial normal subgroup of a finite group contains a minimal normal subgroup:
among the nontrivial normal subgroups contained in `N` (a nonempty family, since `N` is one)
pick one of least cardinality. -/
theorem sz_exists_minimalNormal_le {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (hN : N ≠ ⊥) : ∃ M : Subgroup G, Work.Hall.IsMinimalNormal M ∧ M ≤ N := by
  classical
  -- nontrivial normal subgroups of `G` contained in `N` are nonempty as a family: `N` is one
  have hP : ∃ n : ℕ, ∃ H : Subgroup G, H.Normal ∧ H ≤ N ∧ H ≠ ⊥ ∧ Nat.card H = n :=
    ⟨Nat.card N, N, inferInstance, le_rfl, hN, rfl⟩
  obtain ⟨H, hHn, hHN, hHne, hHcard⟩ := Nat.find_spec hP
  refine ⟨H, ⟨hHn, hHne, ?_⟩, hHN⟩
  intro M hMn hMH hMne
  -- `M` is again a nontrivial normal subgroup contained in `N`, so its order is at least `|H|`
  have hle : Nat.find hP ≤ Nat.card M :=
    Nat.find_min' hP ⟨M, hMn, hMH.trans hHN, hMne, rfl⟩
  have hcard : Nat.card M ≤ Nat.card H := Subgroup.card_le_of_le hMH
  have hEq : Nat.card M = Nat.card H := le_antisymm hcard (hHcard ▸ hle)
  -- equal order together with `M ≤ H` forces `M = H`, hence `H ≤ M`
  exact le_of_eq (Subgroup.eq_of_le_of_card_ge hMH (le_of_eq hEq.symm)).symm

end Work.Hall.SchurZassenhaus
