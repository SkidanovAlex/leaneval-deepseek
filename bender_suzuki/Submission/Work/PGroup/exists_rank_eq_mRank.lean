import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.PGroup

/-- The `p`-rank of a finite group is attained: there is an elementary abelian `p`-subgroup
whose minimal number of generators is exactly `mRank p G`.  This holds for every `p : ℕ`
(for `p = 0` "elementary abelian of exponent `0`" just means abelian, and for `p = 1` only the
trivial subgroup qualifies), because in a finite group there are only finitely many subgroups
and the rank of any subgroup is bounded by `Nat.card G`. -/
theorem exists_rank_eq_mRank {G : Type*} [Group G] [Finite G] (p : ℕ) :
    ∃ E : Subgroup G, Work.PGroup.IsElementaryAbelian p E ∧ Group.rank E = Work.PGroup.mRank p G := by
  classical
  set S : Set ℕ := {n | ∃ E : Subgroup G, Work.PGroup.IsElementaryAbelian p E ∧ Group.rank E = n}
    with hSdef
  have hSne : S.Nonempty := by
    rw [hSdef]
    exact ⟨0, ⊥, Work.PGroup.isElementaryAbelian_bot p, Group.rank_eq_zero _⟩
  have hSfin : S.Finite := by
    refine Set.Finite.subset (Set.finite_Iic (Nat.card G)) ?_
    rintro n ⟨E, _hE, hrank⟩
    rw [Set.mem_Iic, ← hrank]
    haveI : Fintype E := Fintype.ofFinite E
    have hcard : (Finset.univ : Finset E).card = Nat.card E := by
      rw [Finset.card_univ, Nat.card_eq_fintype_card]
    have h := Group.rank_le (G := E) (S := Finset.univ)
      (by rw [Finset.coe_univ]; exact Subgroup.closure_univ)
    rw [hcard] at h
    exact h.trans (Subgroup.card_le_card_group E)
  obtain ⟨E, hE, hrank⟩ := hSne.csSup_mem hSfin
  refine ⟨E, hE, ?_⟩
  rw [hrank, hSdef]
  rfl

end Work.PGroup
