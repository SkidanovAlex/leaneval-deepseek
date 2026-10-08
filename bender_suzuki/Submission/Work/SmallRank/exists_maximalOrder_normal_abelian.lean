import Mathlib
import Submission.Work.SmallRank.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.SmallRank

/-- In a finite group the set of normal abelian subgroups is nonempty (it contains `⊥`) and
finite, so among them there is one of maximal order. -/
theorem exists_maximalOrder_normal_abelian {X : Type*} [Group X] [Finite X] :
    ∃ A : Subgroup X, A.Normal ∧ IsMulCommutative A ∧ (∀ B : Subgroup X, B.Normal → IsMulCommutative B → Nat.card B ≤ Nat.card A) := by
  classical
  let S : Set (Subgroup X) := {B | B.Normal ∧ IsMulCommutative B}
  have hfin : S.Finite := Set.toFinite S
  have hne : S.Nonempty :=
    ⟨⊥, by
      simp only [S, Set.mem_setOf_eq]
      exact ⟨inferInstance, IsMulCommutative.of_comm (fun a b => Subsingleton.elim _ _)⟩⟩
  obtain ⟨A, hA, hmax⟩ :=
    Finset.exists_max_image hfin.toFinset (fun B => Nat.card B) (hfin.toFinset_nonempty.mpr hne)
  rw [Set.Finite.mem_toFinset hfin] at hA
  refine ⟨A, hA.1, hA.2, ?_⟩
  intro B hBn hBc
  exact hmax B (by rw [Set.Finite.mem_toFinset hfin]; exact ⟨hBn, hBc⟩)

end Work.SmallRank
