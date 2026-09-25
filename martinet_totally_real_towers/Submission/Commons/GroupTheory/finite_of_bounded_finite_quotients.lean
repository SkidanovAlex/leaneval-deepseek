import Mathlib.GroupTheory.ResiduallyFinite
import Submission.Commons.GroupTheory.Hopfian.finite_subgroups_of_index_le

set_option linter.style.haveILetI false

namespace Commons.GroupTheory

/-- A finitely generated residually finite group whose finite quotients all have order
bounded by `M` is finite.

Proof. Every finite-index normal subgroup `N` satisfies `Nat.card (G ⧸ N) ≤ M`, hence
`N.index ≤ M`. By `Commons.GroupTheory.Hopfian.finite_subgroups_of_index_le` there are
only finitely many finite-index subgroups of index at most `M`, so there are only
finitely many finite-index normal subgroups `N`. Residually finiteness says
`⨅ N, N = ⊥`, which is now a finite intersection of finite-index subgroups, hence
`⊥` has finite index; equivalently `Nat.card G ≠ 0`, so `G` is finite. -/
theorem finite_of_bounded_finite_quotients (G : Type*) [Group G] [Group.FG G] [Group.ResiduallyFinite G]
    (M : ℕ) (h : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → Nat.card (G ⧸ N) ≤ M) :
    Finite G := by
  classical
  -- There are only finitely many finite-index subgroups of index at most `M`.
  haveI hfin : Finite {H : Subgroup G // H.FiniteIndex ∧ H.index ≤ M} :=
    Hopfian.finite_subgroups_of_index_le M
  -- Hence there are only finitely many finite-index normal subgroups.
  haveI : Finite (FiniteIndexNormalSubgroup G) := by
    refine Finite.of_injective
      (fun H : FiniteIndexNormalSubgroup G =>
        (⟨H.toSubgroup, H.isFiniteIndex', ?_⟩ : {H : Subgroup G // H.FiniteIndex ∧ H.index ≤ M}))
      ?_
    · haveI : H.toSubgroup.FiniteIndex := H.isFiniteIndex'
      have hb : Nat.card (G ⧸ H.toSubgroup) ≤ M :=
        h H.toSubgroup inferInstance
      rw [← Subgroup.index_eq_card] at hb
      exact hb
    · intro H K heq
      exact FiniteIndexNormalSubgroup.toSubgroup_injective (congrArg Subtype.val heq)
  -- Residually finite: `⊥` is the intersection of all finite-index normal subgroups,
  -- a finite intersection.
  have hbot : (⊥ : Subgroup G).FiniteIndex := by
    have hinf := Subgroup.finiteIndex_iInf
      (f := fun H : FiniteIndexNormalSubgroup G => H.toSubgroup) (fun H => H.isFiniteIndex')
    rwa [Group.ResiduallyFinite.iInf_eq_bot] at hinf
  -- A group is finite iff the trivial subgroup has finite index.
  have hcard : Nat.card G ≠ 0 := by
    rw [← Subgroup.index_bot]
    exact hbot.index_ne_zero
  exact Nat.finite_of_card_ne_zero hcard

end Commons.GroupTheory