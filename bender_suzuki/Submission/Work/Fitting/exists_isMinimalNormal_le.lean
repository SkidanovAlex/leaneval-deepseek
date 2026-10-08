import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- Every nontrivial normal subgroup of a finite group contains a minimal normal subgroup:
among the nontrivial normal subgroups of `G` contained in `N` — a nonempty family, since `N`
is one — pick one of least cardinality.  A nontrivial normal subgroup of that minimal one is
again a member of the family, so it has at least its cardinality; being contained in it, it is
equal to it. -/
theorem exists_isMinimalNormal_le (G : Type*) [Group G] [Finite G] {N : Subgroup G}
    (hN : N.Normal) (hne : N ≠ ⊥) :
    ∃ M : Subgroup G, Work.Fitting.IsMinimalNormal M ∧ M ≤ N := by
  classical
  -- the family of nontrivial normal subgroups of `G` contained in `N` is nonempty: `N` is one
  have hP : ∃ n : ℕ, ∃ H : Subgroup G, H.Normal ∧ H ≤ N ∧ H ≠ ⊥ ∧ Nat.card H = n :=
    ⟨Nat.card N, N, hN, le_rfl, hne, rfl⟩
  obtain ⟨H, hHn, hHN, hHne, hHcard⟩ := Nat.find_spec hP
  refine ⟨H, ⟨hHn, hHne, ?_⟩, hHN⟩
  intro M hMn hMH hMne
  -- `M` is again a nontrivial normal subgroup contained in `N`, so its order is at least `|H|`
  have hle : Nat.find hP ≤ Nat.card M :=
    Nat.find_min' hP ⟨M, hMn, hMH.trans hHN, hMne, rfl⟩
  have hcard : Nat.card M ≤ Nat.card H := Subgroup.card_le_of_le hMH
  have hEq : Nat.card M = Nat.card H := le_antisymm hcard (hHcard ▸ hle)
  -- equal order together with `M ≤ H` forces `M = H`
  exact Subgroup.eq_of_le_of_card_ge hMH (le_of_eq hEq.symm)

end Work.Fitting
